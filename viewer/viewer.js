function fail(aMsg) {
  $("#errors").append($("<div>").text(aMsg));
  throw new Error(aMsg);
}

function buildGraph({ svg, points, root, dot, error_message }) {
  let node = $("<div>").addClass("graph");

  // Fill in the graph
  svg = svg.substring(244, svg.length);
  let svgNode = $("<div>")
    .html(svg)
    .appendTo(node);
  svgNode.find("title").first().next().attr("fill", "transparent");

  // Display the error message if any
  if (error_message) {
    $("#errors").append($("<p>").addClass("label").text("Error message:"));
    $("#errors").append($("<pre>").text(error_message));
  }

  // Register stuff for the nodes
  registerNodeHandlers(svgNode, points);

  // The root nodes should be marked with a special color
  if (root) {
    svgNode.find("#node"+root)
      .attr("fill", "#9e2828")
      .css("font-weight", "bold");
  }

  if (dot) {
    let showSource = function (event) {
      let x = event.pageX;
      let y = event.pageY;
      let div = $("<div>")
        .append($("<input type='text'>").val(dot))
        .append($("<span>")
          .text(" (hide)")
          .css("cursor", "pointer")
          .css("font-size", "8pt")
          .click(function () { $(this).parent().remove(); })
        )
        .addClass("popup")
        .css("position", "absolute")
        .css("left", x)
        .css("top", y)
        .appendTo($("body"));
    };
    $("<div>")
      .css("text-align", "right")
      .append(
        $("<a>")
          .text("dot source")
          .addClass("button")
          .click(showSource)
      )
      .appendTo(node);
  }

  return node;
}

function generateLineNumbers() {
  let total = $("#syntax").text().split("\n").length - 2;
  let digits = function (x) (x+"").length;
  let pad = function (x) {
    let str = "";
    let n = digits(total) - digits(x);
    for (let i = 0; i < n; ++i)
      str += " ";
    return str;
  };
  $("#linenos pre").text(
    [pad(i) + i for (i in range(0, total))].join("\n")
  );
}

function fillInterface(aJson) {
  let { type, syntax, current_location, file_name } = aJson;

  $("#filename").text(file_name);

  // Fill in the syntax-highlighted HTML.
  $("#syntax").html(syntax);

  generateLineNumbers();

  // Highlight the sub-expression that was last type-checked.
  highlightLocation(current_location);

  // Display information
  $("#details").text("Last checked expression: "+printLoc(current_location)+" (highlighted).");

  if (type == "single") {
    $("#type").text("a program point");
    // There's only one environment to draw.
    buildGraph(aJson).appendTo($("#graph"));
  } else if (type == "merge") {
    $("#type").text("a merge operation");
    // There's many sub-environments
    $("#subgraphs").show();
    for each (let [i, env] in Iterator(aJson.sub_envs))
      buildGraph(env)
        .prepend($("<p>").addClass("label").text("Sub-environment "+(i+1)))
        .appendTo($("#subgraphs"))

    // That merge into the resulting environment
    buildGraph(aJson.merged_env)
      .prepend($("<p>").addClass("label").text("Merged environment"))
      .appendTo($("#graph"))
  }
}

function registerNodeHandlers(aNode, aPoints) {
  aNode.find(".node > polygon").attr("fill", "white");
  aNode.find(".node").click(function () {
    $(".node > polygon").attr("fill", "white");
    $(this).find("polygon").attr("fill", "#f08a8a");

    let id = $(this).attr("id").match(/node(\d+)/)[1];
    let infos = aPoints[id];
    console.log("Displaying information for node", id);
    displayDetails(infos);
  });
}

function displayDetails(infos) {
  if (!infos) {
    $("#details").text("No information for this node. This is unexpected");
    return;
  }

  let { names, locations, kind, permissions } = infos;

  clearLocations();
  for (let loc of locations)
    highlightLocation(loc);

  $("#details").empty();

  $("#details").append($("<p>").addClass("label2").text("Names"));
  for each (let [, [type, name]] in Iterator(names)) {
    if (type == "user")
      $("#details").append($("<span>").text(name));
    else if (type == "auto")
      $("#details").append($("<i>").text(name));
    $("#details").append($("<span>").text(", "));
  }

  $("#details").append($("<p>").addClass("label2").text("Kind"));
  $("#details").append($("<span>").text(kind));

  $("#details").append($("<p>").addClass("label2").text("Known permissions"));
  let l = $("<ul>");
  for each (let [, t] in Iterator(permissions)) {
    l.append($("<li>").text(t));
  }
  $("#details").append(l);
}

function printPos({ line, col }) {
  return "line "+line+", character "+col;
}

function printLoc({ start, end }) {
  return printPos(start)+", "+printPos(end);
}

function clearLocations() {
  $(".locationBlock").remove();
}

function highlightLocation({ start, end }) {
  let cur = { line: 1, col: 0 };
  let ref = $("#syntax > div").text();
  let before = "";
  let middle = "";
  let after = "";
  for (let i = 0; i < ref.length; ++i) {
    let c;
    if (ref[i] == '\n') {
      // This is a line-break, move accordingly
      cur.line++;
      cur.col = 0;
      c = "\n";
    } else {
      cur.col++;
      c = " ";
    }

    if (cur.line < start.line || (cur.line == start.line && cur.col <= start.col)) {
      before += c;
    } else if (end.line < cur.line || (cur.line == end.line && end.col < cur.col)) {
      after += c;
    } else {
      middle += ref[i];
    }
  }

  let pre = $("<pre />").addClass("locationBlock");
  pre.append($("<span />").text(before));
  pre.append($("<span />").addClass("locationSection").text(middle));

  $("#syntax").append(pre);
}

let zoomFactor = 1;
let zoomStep = .1;

function registerEventHandlers() {
  let resize = function () {
    $(".graph").css("-moz-transform", "scale("+zoomFactor+")");
    $(".graph").each(function () {
      let h = $(this).data("originalHeight");
      if (!h) {
        h = $(this).height();
        $(this).data("originalHeight", h);
      }

      let w = $(this).data("originalWidth");
      if (!w) {
        w = $(this).width();
        $(this).data("originalWidth", w);
      }

      $(this).width(w*zoomFactor);
      $(this).height(h*zoomFactor);
    });
  };

  $("#zoom_out").click(function () {
    zoomFactor -= zoomStep;
    resize();
  });

  $("#zoom_in").click(function () {
    zoomFactor += zoomStep;
    resize();
  });
}

window.addEventListener("load", function () {
  let params = decodeUrlParameters(document.location.href);
  if (!("json_file" in params))
    fail("Please specify the [json_file] parameter in the URL");

  $.getJSON(params.json_file, function (json) {
    fillInterface(json);
    registerEventHandlers();
  });
});
