/* Utility functions */

function log (msg) {
  $("#console").append($("<div>").text(msg));
}


/* Explorer logic */

var files = [
  "corelib/int.mz",
];

$(document).ready(function () {
  var list = $("#explorer ul");
  $.each(files, function (i, f) {
    var item = $("<li>")
      .text(f)
      .click(function () {
        fetch (f);
      });
    list.append(item);
  });
});


/* Main logic */

$(document).ready(function () {
  var editor = ace.edit("editor");
  editor.setTheme("ace/theme/chrome");
  editor.getSession().setMode("ace/mode/ocaml");

  editor.commands.addCommand({
    name: 'make',
    bindKey: {win: 'Ctrl-M',  mac: 'Command-M'},
    exec: function (editor) {
      try {
        var impl = mezzo.lex_and_parse_implementation(editor.getValue());
        mezzo.check_implementation(impl);
        log("Successfully type-checked 😸");
      } catch (e) {
        log("Error 😱 : "+e); 
      }
    },
    readOnly: true
  });

  log("Editor successfully loaded, hit Ctrl-M or Command-M.");
});

