/**
   * Render declutter items for this layer
   * @param {import("../../Map.js").FrameState} frameState Frame state.
   */
renderDeclutter(frameState) {
  const layer = this.getLayer();
  const declutter = layer.getDeclutter();
  if (!declutter || !frameState.declutter) {
    return;
  }

  // Skip declutter during interaction/animation for performance
  const isInteracting = frameState.viewHints[ViewHint.INTERACTING];
  const isAnimating = frameState.viewHints[ViewHint.ANIMATING];
  if (isInteracting || isAnimating) {
    // console.log(`⏸️ renderDeclutter skipped: interacting=${!!isInteracting}, animating=${!!isAnimating}`);
    return;
  }

  // Initialize declutter tree if it doesn't exist or if it's not an RBush instance
  const existingTree = /** @type {any} */ (frameState.declutter[declutter]);
  if (!existingTree || typeof existingTree.getInExtent !== "function") {
    frameState.declutter[declutter] = /** @type {any} */ (new RBush());
  }

  /** @type {import('../../structs/RBush.js').default} */
  const declutterTree = /** @type {any} */ (frameState.declutter[declutter]);
  const source = layer.getSource();

  if (!source) {
    return;
  }

  // Get features and apply declutter logic
  const viewState = frameState.viewState;
  const resolution = viewState.resolution;
  const extent = frameState.extent;

  // Pre-filter features by extent for better performance
  const features = source.getFeaturesInExtent(extent);

  // Process features for decluttering with optimized performance
  const featuresLength = features.length;
  const threshold = 70000;
  // const termId = layer.get("termId");
  // all point geometries and features length is greater than 0
  let filteredFeatures = [];
  let filteredFeaturesLength = 0;
  if (featuresLength === 0) {
    return;
  } else if (featuresLength < threshold) {
    this.declutteredFeatures_ = features;
    for (const feature of features) {
      declutterTree.insert(feature.getGeometry().getExtent(), feature);
    }
    return;
  } else {
    // console.time(`⏱️filter features for term ${termId}`);
    const indexInterval = Math.ceil(featuresLength / threshold);
    filteredFeaturesLength = Math.ceil(featuresLength / indexInterval);
    filteredFeatures = new Array(filteredFeaturesLength);

    // Direct sampling with step - much faster than filter
    for (let i = 0, j = 0; i < featuresLength; i += indexInterval) {
      filteredFeatures[j++] = features[i];
    }
    // console.timeEnd(`⏱️filter features for term ${termId}`);
  }

  // Clear previous declutter entries for this layer only if it's a new frame
  // This prevents clearing entries from other layers in the same declutter group
  if (!this.lastDeclutterFrameState_ || this.lastDeclutterFrameState_ !== frameState) {
    // Only clear if this is the first layer processing this frame
    this.lastDeclutterFrameState_ = frameState;
  }

  // Calculate circle radius once for the layer (not per feature)
  let circleRadius = 8; // default fallback
  const zoom = Math.log2(156543.03392804097 / resolution);

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
          // Create parsing and evaluation contexts
          const parsingContext = newParsingContext();

          // Build the expression evaluator
          const evaluatedRadius = buildExpression(radiusValue, NumberType, parsingContext);

          // Create evaluation context with current map state (no feature-specific data needed for zoom-based expressions)
          const evaluationContext = newEvaluationContext();
          evaluationContext.variables = { zoom: zoom };
          evaluationContext.properties = {}; // Empty for layer-level style
          evaluationContext.resolution = resolution;
          evaluationContext.featureId = null;
          evaluationContext.geometryType = "Point"; // Assume Point for circle radius

          // Evaluate the expression
          const result = evaluatedRadius(evaluationContext);
          if (typeof result === "number" && !isNaN(result)) {
            circleRadius = result;
          }
        } catch (_e) {
          // If expression evaluation fails, try simple cases
          if (radiusValue[0] === "literal" && typeof radiusValue[1] === "number") {
            circleRadius = radiusValue[1];
          } else if (radiusValue[0] === "interpolate" && radiusValue.length >= 6) {
            // For interpolate expressions, manually evaluate
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
          } else if (typeof radiusValue[0] === "number") {
            // Simple array with first element as number
            circleRadius = radiusValue[0];
          }
        }
      }
    }

    // Add stroke width if present
    if (layer.webglStyle_["circle-stroke-width"]) {
      const strokeWidth = layer.webglStyle_["circle-stroke-width"];
      if (typeof strokeWidth === "number") {
        circleRadius += strokeWidth / 2; // Add half stroke width to radius
      }
    }
  }

  // console.time(`⏱️⏱️declutter features for term ${termId}`);
  const declutterBuffer = (circleRadius * resolution) / 8;

  // Pre-allocate declutteredFeatures array with worst-case size
  const declutteredFeatures = new Array(filteredFeaturesLength);
  let declutteredCount = 0;

  // Ultra-optimized path for Point-only features
  let feature, geometry, featureExtent, collisions;
  const declutterExtent = new Array(4); // Reuse array to avoid allocations
  const insertExtent = new Array(4); // Separate array for insertion to avoid slice()

  for (let i = 0; i < filteredFeaturesLength; i++) {
    feature = filteredFeatures[i];
    geometry = feature.getGeometry();

    if (!geometry) continue;

    featureExtent = geometry.getExtent();

    // Inline extent calculation for maximum performance
    declutterExtent[0] = featureExtent[0] - declutterBuffer; // minX
    declutterExtent[1] = featureExtent[1] - declutterBuffer; // minY
    declutterExtent[2] = featureExtent[2] + declutterBuffer; // maxX
    declutterExtent[3] = featureExtent[3] + declutterBuffer; // maxY

    collisions = declutterTree.getInExtent(declutterExtent);

    if (collisions.length === 0) {
      // Copy to insertExtent to avoid modifying declutterExtent
      insertExtent[0] = declutterExtent[0];
      insertExtent[1] = declutterExtent[1];
      insertExtent[2] = declutterExtent[2];
      insertExtent[3] = declutterExtent[3];

      declutterTree.insert(insertExtent, feature);
      declutteredFeatures[declutteredCount++] = feature; // Direct index assignment instead of push
    }
  }

  // Trim array to actual size
  declutteredFeatures.length = declutteredCount;

  // Store decluttered features for rendering
  this.declutteredFeatures_ = declutteredFeatures;
  // console.timeEnd(`⏱️⏱️declutter features for term ${termId}`);

  // Log declutter statistics using _pre-calculated values
  // const visibleCount = declutteredFeatures.length;
  // const totalCount = filteredFeaturesLength;
  // console.log(
  //   `☑️☑️Declutter "${declutter}": ${visibleCount}/${totalCount} features visible (radius: ${circleRadius.toFixed(1)}px, buffer: ${(circleRadius + 1).toFixed(1)}px, zoom: ${zoom.toFixed(1)})`
  // );
}