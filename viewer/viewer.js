function fail(aMsg) {
  $("#errors").append($("<div>").text(aMsg));
  throw new Error(aMsg);
}

function fillInterface(aJson) {
  let {
    svg: svg,
    syntax: syntax,
    current_location: current_location,
    file_name: file_name
  } = aJson;

  $("#heading").append($("<h1>").text("Explanations for "+file_name));

  // Fill in the syntax-highlighted HTML.
  $("#syntax").html(syntax);

  // Fill in the graph
  svg = svg.substring(244, svg.length);
  $("#graph").html(svg);
  $("#graph").find("title").first().next().attr("fill", "transparent");

  // Highlight the sub-expression that was last type-checked.
  highlightLocation(current_location);

  // Display information
  $("#details").text("Last checked expression: "+printLoc(current_location)+" (highlighted).");

  // Register stuff for the nodes
  registerNodeHandlers(aJson);

  // Resize accordingly.
  let w = $(window).width() - $("#syntax").width() - 100;
  $("#details").width(w);
}

function registerNodeHandlers(aJson) {
  $(".node > polygon").attr("fill", "white");
  $(".node").click(function () {
    $(".node > polygon").attr("fill", "white");
    $(this).find("polygon").attr("fill", "#f08a8a");

    let id = $(this).attr("id").match(/node(\d+)/)[1];
    let infos = aJson.points[id];
    console.log("Displaying information for node", id);
    displayDetails(infos);
  });
}

function displayDetails(infos) {
  if (!infos) {
    $("#details").text("No information for this node");
    return;
  }

  let {
    names: names,
    locations: locations,
    kind: kind,
    permissions: permissions
  } = infos;

  clearLocations();
  for (let loc of locations)
    highlightLocation(loc);

  $("#details").empty();

  $("#details").append($("<h2>").text("Names"));
  for each (let [, [type, name]] in Iterator(names)) {
    if (type == "user")
      $("#details").append($("<span>").text(name));
    else if (type == "auto")
      $("#details").append($("<i>").text(name));
    $("#details").append($("<span>").text(", "));
  }

  $("#details").append($("<h2>").text("Kind"));
  $("#details").append($("<strong>").text(kind));

  $("#details").append($("<h2>").text("Known permissions"));
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
  let ref = $("#syntax").text();
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

window.addEventListener("load", function () {
  let params = decodeUrlParameters(document.location.href);
  if (!("json_file" in params))
    fail("Please specify the [json_file] parameter in the URL");

  $.getJSON(params.json_file, function (json) {
    fillInterface(json);
  });
});
