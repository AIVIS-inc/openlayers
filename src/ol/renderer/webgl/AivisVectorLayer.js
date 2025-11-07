/**
 * @module ol/renderer/webgl/AivisVectorLayer
 */

import { assert } from "../../asserts.js";
import { listen, unlistenByKey } from "../../events.js";
import { buffer, createEmpty, equals } from "../../extent.js";
import BaseVector from "../../layer/BaseVector.js";
import { getTransformFromProjections, getUserProjection, toUserExtent, toUserResolution } from "../../proj.js";
import { colorDecodeId } from "../../render/webgl/encodeUtil.js";
import MixedGeometryBatch from "../../render/webgl/MixedGeometryBatch.js";
import VectorStyleRenderer from "../../render/webgl/VectorStyleRenderer.js";
import VectorEventType from "../../source/VectorEventType.js";
import RBush from "../../structs/RBush.js";
import {
  apply as applyTransform,
  create as createTransform,
  makeInverse as makeInverseTransform,
  multiply as multiplyTransform,
  setFromArray as setFromTransform,
  translate as translateTransform,
} from "../../transform.js";
import ViewHint from "../../ViewHint.js";
import { create as createMat4, fromTransform as mat4FromTransform } from "../../vec/mat4.js";
import { DefaultUniform } from "../../webgl/Helper.js";
import WebGLRenderTarget from "../../webgl/RenderTarget.js";
import WebGLLayerRenderer from "./Layer.js";
import { getWorldParameters } from "./worldUtil.js";

export const Uniforms = {
  ...DefaultUniform,
  RENDER_EXTENT: "u_renderExtent", // intersection of layer, source, and view extent
  PATTERN_ORIGIN: "u_patternOrigin",
  GLOBAL_ALPHA: "u_globalAlpha",
};

/**
 * @typedef {import('../../render/webgl/VectorStyleRenderer.js').StyleShaders} StyleShaders
 */
/**
 * @typedef {import('../../style/flat.js').FlatStyleLike | Array<StyleShaders> | StyleShaders} LayerStyle
 */

/**
 * @typedef {Object} Options
 * @property {string} [className='ol-layer'] A CSS class name to set to the canvas element.
 * @property {LayerStyle} style Flat vector style; also accepts shaders
 * @property {Object<string, number|Array<number>|string|boolean>} variables Style variables
 * @property {boolean} [disableHitDetection=false] Setting this to true will provide a slight performance boost, but will
 * prevent all hit detection on the layer.
 * @property {Array<import("./Layer").PostProcessesOptions>} [postProcesses] Post-processes definitions
 */

/**
 * @classdesc
 * Experimental WebGL vector renderer. Supports polygons, lines and points:
 *  Polygons are broken down into triangles
 *  Lines are rendered as strips of quads
 *  Points are rendered as quads
 *
 * You need to provide vertex and fragment shaders as well as custom attributes for each type of geometry. All shaders
 * can access the uniforms in the {@link module:ol/webgl/Helper~DefaultUniform} enum.
 * The vertex shaders can access the following attributes depending on the geometry type:
 *  For polygons: {@link module:ol/render/webgl/PolygonBatchRenderer~Attributes}
 *  For line strings: {@link module:ol/render/webgl/LineStringBatchRenderer~Attributes}
 *  For points: {@link module:ol/render/webgl/PointBatchRenderer~Attributes}
 *
 * Please note that the fragment shaders output should have premultiplied alpha, otherwise visual anomalies may occur.
 *
 * Note: this uses {@link module:ol/webgl/Helper~WebGLHelper} internally.
 */
class AivisWebGLVectorLayerRenderer extends WebGLLayerRenderer {
  /**
   * @param {import("../../layer/Layer.js").default} layer Layer.
   * @param {Options} options Options.
   */
  constructor(layer, options) {
    const uniforms = {
      [Uniforms.RENDER_EXTENT]: [0, 0, 0, 0],
      [Uniforms.PATTERN_ORIGIN]: [0, 0],
      [Uniforms.GLOBAL_ALPHA]: 1,
    };

    super(layer, {
      uniforms: uniforms,
      postProcesses: options.postProcesses,
    });

    /**
     * @type {boolean}
     * @private
     */
    this.hitDetectionEnabled_ = !options.disableHitDetection;

    /**
     * @type {WebGLRenderTarget}
     * @private
     */
    this.hitRenderTarget_;

    /**
     * @private
     */
    this.sourceRevision_ = -1;

    /**
     * @private
     */
    this.previousExtent_ = createEmpty();

    /**
     * @private
     */
    this.renderedExtent_ = createEmpty();

    /**
     * This transform is updated on every frame and is the composition of:
     * - invert of the world->screen transform that was used when rebuilding buffers (see `this.renderTransform_`)
     * - current world->screen transform
     * @type {import("../../transform.js").Transform}
     * @private
     */
    this.currentTransform_ = createTransform();

    /**
     * @private
     */
    this.tmpCoords_ = [0, 0];
    /**
     * @private
     */
    this.tmpTransform_ = createTransform();
    /**
     * @private
     */
    this.tmpMat4_ = createMat4();

    /**
     * @type {import("../../transform.js").Transform}
     * @private
     */
    this.currentFrameStateTransform_ = createTransform();

    /**
     * @type {import('../../style/flat.js').StyleVariables}
     * @private
     */
    this.styleVariables_ = {};

    /**
     * @type {LayerStyle}
     * @private
     */
    this.style_ = [];

    /**
     * @type {VectorStyleRenderer}
     * @public
     */
    this.styleRenderer_ = null;

    /**
     * @type {import('../../render/webgl/VectorStyleRenderer.js').WebGLBuffers}
     * @private
     */
    this.buffers_ = null;

    this.applyOptions_(options);

    /**
     * @private
     */
    this.batch_ = new MixedGeometryBatch();

    /**
     * @private
     * @type {boolean}
     */
    this.initialFeaturesAdded_ = false;

    /**
     * @private
     * @type {Array<import("../../events.js").EventsKey|null>}
     */
    this.sourceListenKeys_ = null;

    /**
     * @private
     * @type {number}
     */
    this.totalFeaturesCount_ = 0;

    /**
     * @private
     * @type {Array<import("../../Feature.js").FeatureLike>}
     */
    this.features4Tier1_ = null;

    /**
     * @private
     * @type {Array<import("../../Feature.js").FeatureLike>}
     */
    this.features4Tier2_ = null;

    /**
     * @private
     * @type {Array<import("../../Feature.js").FeatureLike>}
     */
    this.feature4Tier3_ = null;

    /**
     * @private
     * @type {boolean}
     */
    this.shouldUseFiltering_ = false;

    /**
     * @private
     * @type {number}
     */
    this.maxZoom_ = -1;

    /**
     * @private
     * @type {number}
     */
    this.previousZoom_ = -1;

    /**
     * @private
     * @type {boolean}
     */
    this.needsBatchUpdate_ = false;

    /**
     * @private
     * @type {boolean}
     */
    this.isBatchUpdatePending_ = false;

    /**
     * @private
     * @type {Array<import("../../Feature.js").FeatureLike>}
     */
    this.currentFeaturesToRender_ = null;

    /**
     * @private
     * @type {number}
     */
    this.fixedCount_ = 0;

    /**
     * @private
     * @type {number}
     */
    this.pendingFrame_ = 10;

    /**
     * @private
     * @type {import('../../structs/RBush.js').default}
     */
    this.declutterTree_ = new RBush();
  }

  /**
   * Initialize and cache maxZoom from the map's view (called once)
   * Sets this.maxZoom_ property
   * @private
   */
  getMaxZoom_() {
    // Already initialized
    if (this.maxZoom_ > 0) {
      return this.maxZoom_;
    }

    // Try to get maxZoom from the map's view
    let maxZoom = 5; // Default fallback for WSI
    try {
      const layer = this.getLayer();
      const mapFromLayer = layer.getMapInternal();
      if (mapFromLayer) {
        const view = mapFromLayer.getView();
        if (view) {
          const viewMaxZoom = view.getMaxZoom();
          if (viewMaxZoom && viewMaxZoom > 0) {
            maxZoom = viewMaxZoom;
          }
        }
      }
    } catch (e) {
      console.warn("Unable to get maxZoom from map, using default:", e);
    }

    // Cache the value
    this.maxZoom_ = maxZoom;
    return maxZoom;
  }

  /**
   * Apply declutter logic to features
   * @private
   * @param {Array<import("../../Feature.js").FeatureLike>} features Features to declutter
   * @param {number} resolution Current resolution
   * @return {Array<import("../../Feature.js").FeatureLike>} Decluttered features
   */
  applyDeclutter_(features, resolution) {
    this.declutterTree_.clear();

    const featuresLength = features.length;

    // Calculate circle radius dynamically from layer style
    let circleRadius = 8; // default fallback
    const zoom = Math.log2(156543.03392804097 / resolution);
    const layer = this.getLayer();

    if (layer && layer.webglStyle_) {
      const flatStyle = layer.webglStyle_;

      // Check if it's a flat style object with circle-radius
      if (typeof flatStyle === "object" && flatStyle["circle-radius"] !== undefined) {
        const radiusValue = flatStyle["circle-radius"];

        // Handle different types of radius values
        if (typeof radiusValue === "number") {
          circleRadius = radiusValue;
        } else if (Array.isArray(radiusValue)) {
          try {
            // Handle interpolate expressions manually
            if (radiusValue[0] === "interpolate" && radiusValue.length >= 6) {
              // ['interpolate', ['linear'], ['zoom'], 0, 0.1, 22, 7]
              const stops = [];
              for (let i = 3; i < radiusValue.length; i += 2) {
                if (i + 1 < radiusValue.length) {
                  stops.push([radiusValue[i], radiusValue[i + 1]]);
                }
              }
              // Simple linear interpolation
              if (stops.length >= 2) {
                if (zoom <= stops[0][0]) {
                  circleRadius = stops[0][1];
                } else if (zoom >= stops[stops.length - 1][0]) {
                  circleRadius = stops[stops.length - 1][1];
                } else {
                  // Find the right interval and interpolate
                  for (let i = 0; i < stops.length - 1; i++) {
                    if (zoom >= stops[i][0] && zoom <= stops[i + 1][0]) {
                      const t = (zoom - stops[i][0]) / (stops[i + 1][0] - stops[i][0]);
                      circleRadius = stops[i][1] + t * (stops[i + 1][1] - stops[i][1]);
                      break;
                    }
                  }
                }
              }
            } else if (radiusValue[0] === "literal" && typeof radiusValue[1] === "number") {
              circleRadius = radiusValue[1];
            } else if (typeof radiusValue[0] === "number") {
              // Simple array with first element as number
              circleRadius = radiusValue[0];
            }
          } catch (_e) {
            // Keep default radius if parsing fails
          }
        }
      }

      // Add stroke width if present
      if (flatStyle["circle-stroke-width"]) {
        const strokeWidth = flatStyle["circle-stroke-width"];
        if (typeof strokeWidth === "number") {
          circleRadius += strokeWidth / 2; // Add half stroke width to radius
        }
      }
    }

    const declutterBuffer = (circleRadius * resolution) / 8;

    // Pre-allocate declutteredFeatures array
    const declutteredFeatures = new Array(featuresLength);
    let declutteredCount = 0;

    // Reuse arrays to avoid allocations
    const declutterExtent = new Array(4);
    const insertExtent = new Array(4);

    for (let i = 0; i < featuresLength; i++) {
      const feature = features[i];
      try {
        const geometry = feature.getGeometry();

        if (!geometry) continue;

        const featureExtent = geometry.getExtent();

        // Calculate declutter extent with buffer
        declutterExtent[0] = featureExtent[0] - declutterBuffer; // minX
        declutterExtent[1] = featureExtent[1] - declutterBuffer; // minY
        declutterExtent[2] = featureExtent[2] + declutterBuffer; // maxX
        declutterExtent[3] = featureExtent[3] + declutterBuffer; // maxY

        const collisions = this.declutterTree_.getInExtent(declutterExtent);

        if (collisions.length === 0) {
          // Copy to insertExtent
          insertExtent[0] = declutterExtent[0];
          insertExtent[1] = declutterExtent[1];
          insertExtent[2] = declutterExtent[2];
          insertExtent[3] = declutterExtent[3];

          this.declutterTree_.insert(insertExtent, feature);
          declutteredFeatures[declutteredCount++] = feature;
        }
      } catch (e) {
        console.error("Error getting geometry for feature", feature, e);
      }
    }

    // Trim array to actual size
    declutteredFeatures.length = declutteredCount;

    return declutteredFeatures;
  }

  /**
   * Update batch with features in worker-style async manner
   * @private
   * @param {Array<import("../../Feature.js").FeatureLike>} features Features to add to batch
   * @param {import("../../proj.js").TransformFunction} projectionTransform Transform function
   * @return {Promise<void>}
   */
  updateBatchAsync_(features, projectionTransform) {
    return new Promise(resolve => {
      // Use setTimeout to defer work to next tick (worker-style async)
      setTimeout(() => {
        console.log("rendered features length", features.length);
        this.batch_.clear();
        this.batch_.addFeatures(features, projectionTransform);
        resolve();
      }, 0);
    });
  }

  /**
   * Process features for current zoom tier in worker-style async manner
   * Does NOT block prepareFrameInternal - runs completely async
   * Handles: feature filtering + declutter + batch update + buffer generation
   * @private
   * @param {number} currentZoomTier Current zoom tier
   * @param {import("../../Map.js").FrameState} frameState Frame state
   * @param {import("../../source/Vector.js").default} vectorSource Vector source
   */
  processFeaturesForZoomTier_(currentZoomTier, frameState, vectorSource) {
    if (this.isBatchUpdatePending_) {
      return;
    }

    this.isBatchUpdatePending_ = true;
    this.ready = false;

    // Use setTimeout to defer heavy computation (worker-style async)
    setTimeout(() => {
      const resolution = frameState.viewState.resolution;
      let featuresToRender;

      if (currentZoomTier === 0) {
        // High zoom: use viewport extent with buffer
        const bufferRatio = 0.3;
        const widthBuffer = (frameState.extent[2] - frameState.extent[0]) * bufferRatio;
        const heightBuffer = (frameState.extent[3] - frameState.extent[1]) * bufferRatio;
        const extent = [frameState.extent[0] - widthBuffer, frameState.extent[1] - heightBuffer, frameState.extent[2] + widthBuffer, frameState.extent[3] + heightBuffer];
        featuresToRender = vectorSource.getFeaturesInExtent(extent);
        this.pendingFrame_ = 2;
      } else {
        featuresToRender = this.features4Tier3_;
        switch (currentZoomTier) {
          case 1:
            featuresToRender = this.features4Tier1_;
            break;
          case 2:
            featuresToRender = this.features4Tier2_;
            break;
          default:
            featuresToRender = this.features4Tier3_;
            break;
        }
        featuresToRender = this.applyDeclutter_(featuresToRender, resolution);
        this.pendingFrame_ = 10;
      }

      this.currentFeaturesToRender_ = featuresToRender;

      // Update batch (also async)
      const userProjection = getUserProjection();
      let projectionTransform;
      if (userProjection) {
        projectionTransform = getTransformFromProjections(userProjection, frameState.viewState.projection);
      }

      this.updateBatchAsync_(featuresToRender, projectionTransform).then(() => {
        // Generate buffers after batch is ready - all in worker
        const transform = this.helper.makeProjectionTransform(frameState, createTransform());

        this.styleRenderer_.generateBuffers(this.batch_, transform).then(buffers => {
          if (this.buffers_) {
            this.disposeBuffers(this.buffers_);
          }
          this.buffers_ = buffers;
          this.ready = true;
          this.isBatchUpdatePending_ = false;
          this.needsBatchUpdate_ = false;
          this.getLayer().changed();
        });
      });
    }, 0);
  }

  /**
   * @private
   * @param {import("../../source/Vector.js").default} source Source.
   */
  prepareFilteredFeatures_(source) {
    const allFeatures = source.getFeatures();

    if (allFeatures.length === this.totalFeaturesCount_) {
      return;
    }

    // Store total feature count on first load and create 3-tier filtered feature lists
    this.totalFeaturesCount_ = allFeatures.length;

    // 1. If less than 30,000 features, render all without filtering
    if (this.totalFeaturesCount_ < 50_000) {
      this.shouldUseFiltering_ = false;
      // console.log(`✅ Rendering all ${this.totalFeaturesCount_} features (< 30,000, no filtering)`);
    } else {
      // 2. Create 3-tier filtered feature lists (30k, 50k, 100k)
      this.shouldUseFiltering_ = true;
      // console.log(`🎯 Creating 3-tier filtered lists for ${this.totalFeaturesCount_} features`);

      // Helper function to add features not in previous set
      const addAdditionalFeatures = (targetCount, previousIndices, allFeatures, previousFeatures) => {
        const maxCount = Math.min(targetCount, this.totalFeaturesCount_);
        const additionalNeeded = maxCount - previousFeatures.length;
        const resultArray = new Array(maxCount);

        // First, copy all previous features
        let j = 0;
        for (let i = 0; i < previousFeatures.length; i++) {
          resultArray[j++] = previousFeatures[i];
        }

        // Then, add additional features not in previous set
        if (additionalNeeded > 0) {
          const availableIndices = this.totalFeaturesCount_ - previousIndices.size;
          const indexInterval = Math.max(1, Math.floor(availableIndices / additionalNeeded));

          let added = 0;
          for (let i = 0; i < this.totalFeaturesCount_ && added < additionalNeeded; i++) {
            if (!previousIndices.has(i) && i % indexInterval === 0) {
              resultArray[j++] = allFeatures[i];
              previousIndices.add(i);
              added++;
            }
          }

          // If still need more, add remaining features
          if (added < additionalNeeded) {
            for (let i = 0; i < this.totalFeaturesCount_ && j < maxCount; i++) {
              if (!previousIndices.has(i)) {
                resultArray[j++] = allFeatures[i];
                previousIndices.add(i);
              }
            }
          }
        }

        resultArray.length = j;
        return resultArray;
      };

      // 2-1. Create 1/3 of total features feature list
      const featuresLengthTier3 = Math.min(50_000, Math.ceil((1 / 5) * this.totalFeaturesCount_));
      const intervalTier3 = Math.ceil(this.totalFeaturesCount_ / featuresLengthTier3);
      this.features4Tier3_ = new Array(featuresLengthTier3);
      const features4Tier3_ = new Set();

      for (let i = 0, j = 0; i < this.totalFeaturesCount_; i += intervalTier3) {
        this.features4Tier3_[j++] = allFeatures[i];
        features4Tier3_.add(i);
      }

      // 2-2. Create 1/2 feature list (includes all 30k features)
      const featuresLengthTier2 = Math.min(100_000, Math.ceil((2 / 5) * this.totalFeaturesCount_));
      this.features4Tier2_ = addAdditionalFeatures(featuresLengthTier2, features4Tier3_, allFeatures, this.features4Tier3_);

      // 2-3. Create 100,000 feature list (includes all 50k features)
      const featuresLengthTier1 = Math.min(200_000, Math.ceil((1 / 2) * this.totalFeaturesCount_));
      this.features4Tier1_ = addAdditionalFeatures(featuresLengthTier1, features4Tier3_, allFeatures, this.features4Tier2_);

      console.log(`✅ Filtered lists: Tier 3=${this.features4Tier3_.length}, Tier 2=${this.features4Tier2_.length}, Tier 1=${this.features4Tier1_.length}`);
    }
  }

  /**
   * @private
   * @param {import("../../proj.js").TransformFunction} projectionTransform Transform function.
   */
  addInitialFeatures_(projectionTransform) {
    const source = this.getLayer().getSource();

    this.prepareFilteredFeatures_(source);

    this.sourceListenKeys_ = [
      listen(source, VectorEventType.ADDFEATURE, this.handleSourceFeatureAdded_.bind(this, projectionTransform)),
      listen(source, VectorEventType.CHANGEFEATURE, this.handleSourceFeatureChanged_.bind(this, projectionTransform), this),
      listen(source, VectorEventType.REMOVEFEATURE, this.handleSourceFeatureDelete_, this),
      listen(source, VectorEventType.CLEAR, this.handleSourceFeatureClear_, this),
    ];
  }

  /**
   * @param {Options} options Options.
   * @private
   */
  applyOptions_(options) {
    this.styleVariables_ = options.variables;
    this.style_ = options.style;
  }

  /**
   * @private
   */
  createRenderers_() {
    this.buffers_ = null;
    this.styleRenderer_ = new VectorStyleRenderer(this.style_, this.styleVariables_, this.helper, this.hitDetectionEnabled_);
  }

  /**
   * @override
   */
  reset(options) {
    this.applyOptions_(options);
    if (this.helper) {
      this.createRenderers_();
    }
    super.reset(options);
  }

  /**
   * @override
   */
  afterHelperCreated() {
    if (this.styleRenderer_) {
      // To reuse buffers
      this.styleRenderer_.setHelper(this.helper, this.buffers_);
    } else {
      this.createRenderers_();
    }

    if (this.hitDetectionEnabled_) {
      this.hitRenderTarget_ = new WebGLRenderTarget(this.helper);
    }
  }

  /**
   * @param {import("../../proj.js").TransformFunction} projectionTransform Transform function.
   * @param {import("../../source/Vector.js").VectorSourceEvent} event Event.
   * @private
   */
  handleSourceFeatureAdded_(projectionTransform, event) {
    this.addInitialFeatures_(projectionTransform);
    this.initialFeaturesAdded_ = true;
  }

  /**
   * @param {import("../../proj.js").TransformFunction} projectionTransform Transform function.
   * @param {import("../../source/Vector.js").VectorSourceEvent} event Event.
   * @private
   */
  handleSourceFeatureChanged_(projectionTransform, event) {
    const feature = event.feature;
    this.batch_.changeFeature(feature, projectionTransform);
  }

  /**
   * @param {import("../../source/Vector.js").VectorSourceEvent} event Event.
   * @private
   */
  handleSourceFeatureDelete_(event) {
    const feature = event.feature;
    this.batch_.removeFeature(feature);
  }

  /**
   * @private
   */
  handleSourceFeatureClear_() {
    this.batch_.clear();
  }

  /**
   * @param {import("../../transform.js").Transform} batchInvertTransform Inverse of the transformation in which geometries are expressed
   * @private
   */
  applyUniforms_(batchInvertTransform) {
    // world to screen matrix
    setFromTransform(this.tmpTransform_, this.currentFrameStateTransform_);
    multiplyTransform(this.tmpTransform_, batchInvertTransform);
    this.helper.setUniformMatrixValue(Uniforms.PROJECTION_MATRIX, mat4FromTransform(this.tmpMat4_, this.tmpTransform_));

    // screen to world matrix
    makeInverseTransform(this.tmpTransform_, this.tmpTransform_);
    this.helper.setUniformMatrixValue(Uniforms.SCREEN_TO_WORLD_MATRIX, mat4FromTransform(this.tmpMat4_, this.tmpTransform_));

    // pattern origin should always be [0, 0] in world coordinates
    this.tmpCoords_[0] = 0;
    this.tmpCoords_[1] = 0;
    makeInverseTransform(this.tmpTransform_, batchInvertTransform);
    applyTransform(this.tmpTransform_, this.tmpCoords_);
    this.helper.setUniformFloatVec2(Uniforms.PATTERN_ORIGIN, this.tmpCoords_);
  }

  /**
   * Render the layer.
   * @param {import("../../Map.js").FrameState} frameState Frame state.
   * @return {HTMLElement} The rendered element.
   * @override
   */
  renderFrame(frameState) {
    const gl = this.helper.getGL();
    this.preRender(gl, frameState);

    const [startWorld, endWorld, worldWidth] = getWorldParameters(frameState, this.getLayer());

    // draw the normal canvas
    this.helper.prepareDraw(frameState);
    this.renderWorlds(frameState, false, startWorld, endWorld, worldWidth);
    this.helper.finalizeDraw(frameState, this.dispatchPreComposeEvent, this.dispatchPostComposeEvent);

    const canvas = this.helper.getCanvas();

    if (this.hitDetectionEnabled_) {
      this.renderWorlds(frameState, true, startWorld, endWorld, worldWidth);
      this.hitRenderTarget_.clearCachedData();
    }

    this.postRender(gl, frameState);

    return canvas;
  }

  /**
   * Determine whether renderFrame should be called.
   * @param {import("../../Map.js").FrameState} frameState Frame state.
   * @return {boolean} Layer is ready to be rendered.
   * @override
   */
  prepareFrameInternal(frameState) {
    const layer = this.getLayer();
    const vectorSource = layer.getSource();
    const viewState = frameState.viewState;
    const currentExtent = frameState.extent.slice();
    const isViewPortMoving = frameState.viewHints[ViewHint.ANIMATING] || frameState.viewHints[ViewHint.INTERACTING] || !equals(this.previousExtent_, currentExtent);
    const sourceChanged = this.sourceRevision_ < vectorSource.getRevision();

    if (!sourceChanged) {
      if (isViewPortMoving) {
        this.previousExtent_ = currentExtent;
        this.getLayer().changed();
        this.fixedCount_ = 0;
        return true;
      } else if (equals(this.renderedExtent_, currentExtent)) {
        this.fixedCount_ = 0;
        return true;
      }
    }

    if (this.fixedCount_++ < this.pendingFrame_) {
      this.getLayer().changed();
      return true;
    }

    this.fixedCount_ = 0;

    this.sourceRevision_ = vectorSource.getRevision();
    if (this.totalFeaturesCount_ !== vectorSource.getFeatures().length) {
      this.prepareFilteredFeatures_(vectorSource);
    }

    const projection = viewState.projection;
    const resolution = viewState.resolution;

    const renderBuffer = layer instanceof BaseVector ? layer.getRenderBuffer() : 0;
    const extent = buffer(frameState.extent, renderBuffer * resolution);

    const userProjection = getUserProjection();
    if (userProjection) {
      vectorSource.loadFeatures(toUserExtent(extent, userProjection), toUserResolution(resolution, projection), userProjection);
    } else {
      vectorSource.loadFeatures(extent, resolution, projection);
    }

    this.ready = false;

    const maxZoom = this.getMaxZoom_();
    const currentZoom = frameState.viewState.zoom;
    // tier 3: 0-70%
    // tier 2: 70-90%
    // tier 1: 90-100%
    // tier 0: 100%
    const currentZoomTier = currentZoom >= (maxZoom * 7) / 10 ? 0 : currentZoom >= (maxZoom * 5) / 10 ? 1 : currentZoom >= (maxZoom * 3) / 10 ? 2 : 3;

    if (
      (this.shouldUseFiltering_ && !this.isBatchUpdatePending_ && currentZoomTier !== 0 && currentZoom !== this.previousZoom_) ||
      (currentZoomTier === 0 && !equals(this.renderedExtent_, frameState.extent))
    ) {
      this.processFeaturesForZoomTier_(currentZoomTier, frameState, vectorSource);
      this.previousZoom_ = currentZoom;
      this.renderedExtent_ = frameState.extent.slice();

      const transform = this.helper.makeProjectionTransform(frameState, createTransform());

      this.styleRenderer_.generateBuffers(this.batch_, transform).then(buffers => {
        if (this.buffers_) {
          this.disposeBuffers(this.buffers_);
        }
        this.buffers_ = buffers;
        this.ready = true;
        this.getLayer().changed();
      });
    }

    this.previousExtent_ = currentExtent;
    return true;
  }

  /**
   * Render the world, either to the main framebuffer or to the hit framebuffer
   * @param {import("../../Map.js").FrameState} frameState current frame state
   * @param {boolean} forHitDetection whether the rendering is for hit detection
   * @param {number} startWorld the world to render in the first iteration
   * @param {number} endWorld the last world to render
   * @param {number} worldWidth the width of the worlds being rendered
   */
  renderWorlds(frameState, forHitDetection, startWorld, endWorld, worldWidth) {
    let world = startWorld;

    if (forHitDetection) {
      this.hitRenderTarget_.setSize([Math.floor(frameState.size[0] / 2), Math.floor(frameState.size[1] / 2)]);
      this.helper.prepareDrawToRenderTarget(frameState, this.hitRenderTarget_, true);
    }

    do {
      this.helper.makeProjectionTransform(frameState, this.currentFrameStateTransform_);
      translateTransform(this.currentFrameStateTransform_, world * worldWidth, 0);
      if (!this.buffers_) {
        continue;
      }
      this.styleRenderer_.render(this.buffers_, frameState, () => {
        this.applyUniforms_(this.buffers_.invertVerticesTransform);
        this.helper.applyHitDetectionUniform(forHitDetection);
      });
    } while (++world < endWorld);
  }

  /**
   * @param {import("../../coordinate.js").Coordinate} coordinate Coordinate.
   * @param {import("../../Map.js").FrameState} frameState Frame state.
   * @param {number} hitTolerance Hit tolerance in pixels.
   * @param {import("../vector.js").FeatureCallback<T>} callback Feature callback.
   * @param {Array<import("../Map.js").HitMatch<T>>} matches The hit detected matches with tolerance.
   * @return {T|undefined} Callback result.
   * @template T
   * @override
   */
  forEachFeatureAtCoordinate(coordinate, frameState, hitTolerance, callback, matches) {
    assert(this.hitDetectionEnabled_, "`forEachFeatureAtCoordinate` cannot be used on a WebGL layer if the hit detection logic has been disabled using the `disableHitDetection: true` option.");
    if (!this.styleRenderer_ || !this.hitDetectionEnabled_) {
      return undefined;
    }

    const pixel = applyTransform(frameState.coordinateToPixelTransform, coordinate.slice());

    const data = this.hitRenderTarget_.readPixel(pixel[0] / 2, pixel[1] / 2);
    const color = [data[0] / 255, data[1] / 255, data[2] / 255, data[3] / 255];
    const ref = colorDecodeId(color);
    const feature = this.batch_.getFeatureFromRef(ref);
    if (feature) {
      return callback(feature, this.getLayer(), null);
    }
    return undefined;
  }

  /**
   * Will release a set of Webgl buffers
   * @param {import('../../render/webgl/VectorStyleRenderer.js').WebGLBuffers} buffers Buffers
   */
  disposeBuffers(buffers) {
    /**
     * @param {Array<import('../../webgl/Buffer.js').default>} typeBuffers Buffers
     */
    const disposeBuffersOfType = typeBuffers => {
      for (const buffer of typeBuffers) {
        if (buffer) {
          this.helper.deleteBuffer(buffer);
        }
      }
    };
    if (buffers.pointBuffers) {
      disposeBuffersOfType(buffers.pointBuffers);
    }
    if (buffers.lineStringBuffers) {
      disposeBuffersOfType(buffers.lineStringBuffers);
    }
    if (buffers.polygonBuffers) {
      disposeBuffersOfType(buffers.polygonBuffers);
    }
  }

  /**
   * Clean up.
   * @override
   */
  disposeInternal() {
    if (this.buffers_) {
      this.disposeBuffers(this.buffers_);
    }
    if (this.sourceListenKeys_) {
      this.sourceListenKeys_.forEach(function (key) {
        unlistenByKey(key);
      });
      this.sourceListenKeys_ = null;
    }
    super.disposeInternal();
  }
}

export default AivisWebGLVectorLayerRenderer;
