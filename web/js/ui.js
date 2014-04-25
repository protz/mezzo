// Some value are set from ocaml
// mezzo.beforeInit
// mezzo.afterInit
// mezzo.process (typecheck & interpret function)
// mezzo.files (the files to display on the explorer)

// Modules from Ace that we need
var Range = ace.require("./range").Range;

// The main driver for type-checking something.
function mz_on_make(){
  var typecheck = $("#option-typecheck").prop("checked");
  var interpret = $("#option-interpret").prop("checked");
  if(!mezzo.process) { alert("Mezzo is not initialized") };
  mezzo.process(
    editor.getValue(),
    typecheck,
    interpret,
    parseInt($("#option-debug").val()),
    $("#option-warnerror").val()
  );
}

//Setup the Ace editor.
function mz_setup_editor () {
  editor = ace.edit("editor");
  editor.setTheme("ace/theme/chrome");
  editor.getSession().setMode("ace/mode/ocaml");

  editor.commands.addCommand({
    name: 'make',
    bindKey: {win: 'Ctrl-M',  mac: 'Command-M'},
    exec: mz_on_make,
    readOnly: true
  });
  editor.focus();
};

// (called by ocaml)
function mz_highlight_range(r1, c1, r2, c2) {
  editor.getSelection().addRange(new Range(r1, c1, r2, c2));
};

//Logs (called by ocaml)
function mz_log(content,classes) {
  var console = $("#console");
  buf = $("<div />")
    .text(content)
    .addClass(classes)
    .appendTo(console);
  console.scrollTop(console.prop("scrollHeight"));
}

//Clear console
function mz_clear() {
  $("#console").empty()
}

// Builds the left pane with the list of files that can be loaded into the
// editor.
function mz_build_explorer(dirs){

  var list = $("#explorer ul");
  $.each(dirs, function (i,dir) {
    var item = $("<li>");
    item.append($("<span />").text(dir.name));
    item.append($("<span />").text(" "));
    var collapsed = false;
    item.append($("<a href='#' style='font-size: 80%'></a>")
                .text("(collapse)")
                .addClass("toggle")
                .click(function () {
                  $(this).next().toggle();
                  collapsed = !collapsed;
                  $(this).text(collapsed ? "(expand)" : "(collapse)");
                })
               );
    list.append(item);

    var sublist = $("<ul>")
        .addClass("file-list");
    $.each(dir.files, function (i, f) {
      var item = $("<li>");
      item.append($("<a href='#'></a>")
                  .text(f.name)
                  .click(function () {
                    var source = f.content;
                    editor.setValue(source);
                    editor.clearSelection();
                    editor.gotoLine(0);
                  })
                 );
      sublist.append(item);
    });
    item.append(sublist);

    if (dir.name == "corelib" || dir.name == "stdlib")
      item.find("a.toggle").click();
  });
  list.prepend($("<li>").append(
    $("<a href='#'>")
      .text("new")
      .click(function () {
        editor.setValue("");
      })));
};

$(document).ready(function () {
  if(mezzo.beforeInit)
    mezzo.beforeInit();

  // Register all event listeners + default values
  $("#command-clear").click(mz_clear);
  $("#command-go").click(mz_on_make);
  $("#option-typecheck").prop("checked", true);
  $("#option-warnerror").val("-1+2..4-5+6");
  $("#show-more-options").click(function () {
    $(this).next().show("slow");
    $(this).remove();
  });
  if(mezzo.files)
    mz_build_explorer(mezzo.files);
  mz_setup_editor();

  if(mezzo.afterInit)
    mezzo.afterInit();
});
