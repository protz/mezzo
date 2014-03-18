var mezzo_editor;

var mezzo_ui = (function () {
  var files = {
    "corelib": [
      "array.mz",
      "array.mzi",
      "autoarray.mz",
      "autoarray.mzi",
      "autoload",
      "bool.mz",
      "bool.mzi",
      "info.mz",
      "info.mzi",
      "int.mz",
      "int.mzi",
      "lock.mz",
      "lock.mzi",
      "magic.mz",
      "magic.mzi",
      "myocamlbuild.ml",
      "nest.mz",
      "nest.mzi",
      "option.mz",
      "option.mzi",
      "physical.mz",
      "physical.mzi",
      "pool.mz",
      "print.mz",
      "print.mzi",
      "ref.mz",
      "ref.mzi",
      "thread.mz",
      "thread.mzi",
      "tube.mz",
      "tube.mzi",
    ],

    "stdlib": [
      "bfs.mz",
      "bfs.mzi",
      "bucket.mz",
      "bucket.mzi",
      "channel.mz",
      "channel.mzi",
      "condition.mz",
      "condition.mzi",
      "control.mz",
      "dfs.mz",
      "dfs.mzi",
      "doublylinked.mz",
      "doublylinked.mzi",
      "either.mz",
      "either.mzi",
      "fix.mz",
      "focused.mz",
      "focused.mzi",
      "hashtable.mz",
      "hashtable.mzi",
      "hide.mz",
      "hide.mzi",
      "iterator.mz",
      "iterator.mzi",
      "lazy.mz",
      "lazy.mzi",
      "list.mz",
      "list.mzi",
      "Makefile",
      "memoize.mz",
      "memoize.mzi",
      "mlist.mz",
      "mlist.mzi",
      "mutableTreeMap.mz",
      "mutableTreeMap.mzi",
      "name.mz",
      "name.mzi",
      "osf.mz",
      "osf.mzi",
      "partition.mz",
      "persistentarray.mz",
      "persistentarray.mzi",
      "pool.mzi",
      "protected.mz",
      "protected.mzi",
      "queue.mz",
      "queue.mzi",
      "reflection.mz",
      "reflection.mzi",
      "stash.mz",
      "stash.mzi",
      "stream.mz",
      "stream.mzi",
      "string.mz",
      "string.mzi",
      "synctube.mz",
      "synctube.mzi",
      "vector.mz",
      "vector.mzi",
      "wref.mz",
      "wref.mzi",
    ],
  };

  var src_dir = "";

  var mezzo_ui = {
    /* Utility functions */
    log: function (msg) {
      $("#console").append($("<div>").text(msg));
    },

    fetch: function (file, k) {
      $.ajax({
        url: src_dir+file,
        success: function (data, textStatus) {
          k(data);
        },
        dataType: "html"
      });
    },

    fetch_and_load: function (file) {
      mezzo_ui.fetch(file, function (source) {
        mezzo_editor.setValue(source);
        mezzo_editor.clearSelection();
        mezzo_editor.gotoLine(0);
      });
    },

    files: files,

    on_make: function (editor) {
      try {
        var impl = mezzo.lex_and_parse_implementation(editor.getValue());
        mezzo.check_implementation(impl);
        mezzo_ui.log("Successfully type-checked 😸");
      } catch (e) {
        mezzo_ui.log("Error 😱 : "+e); 
      }
    }
  };
  return mezzo_ui;
})();


$(document).ready(function () {
  /* Explorer logic */
  var list = $("#explorer ul");
  $.each(mezzo_ui.files, function (folder, files) {
    var item = $("<li>");
    item.append($("<span />").text(folder));
    item.append($("<span />").text(" "));
    var collapsed = false;
    item.append($("<a href='#' style='font-size: 80%'></a>")
      .text("(collapse)")
      .click(function () {
        $(this).next().toggle();
        collapsed = !collapsed;
        $(this).text(collapsed ? "(expand)" : "(collapse)");
      })
    );
    list.append(item);

    var sublist = $("<ul>");
    $.each(files, function (i, f) {
      var item = $("<li>");
      item.append($("<a href='#'></a>")
        .text(f)
        .click(function () {
          mezzo_ui.fetch_and_load(folder+"/"+f);
        })
      );
      sublist.append(item);
    });
    item.append(sublist);
  });

  /* Main logic */
  var editor = ace.edit("editor");
  editor.setTheme("ace/theme/chrome");
  editor.getSession().setMode("ace/mode/ocaml");

  editor.commands.addCommand({
    name: 'make',
    bindKey: {win: 'Ctrl-M',  mac: 'Command-M'},
    exec: mezzo_ui.on_make,
    readOnly: true
  });

  // Assign into the global.
  mezzo_editor = editor;

  mezzo_ui.log("Editor successfully loaded, hit Ctrl-M or Command-M.");
});

