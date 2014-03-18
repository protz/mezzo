var mezzo_fs_get;
var mezzo_ui_log;
var mezzo_ret_code;

(function () {
  "use strict";

  // The Ace editor.
  var editor;

  // A glue to hide the fact that there is no filesystem, only files that can be
  // fetched over http.
  var fs_cache = {};
  var fs = {
    fetch: function (file, k) {
      if (file in fs_cache) {
        k(fs_cache[file]);
      } else {
        $.ajax({
          url: src_dir+file,
          success: function (data, textStatus) {
            fs_cache[file] = data;
            k(data);
          },
          dataType: "html"
        });
      }
    },

    get: function(file) {
      if (!(file in fs_cache))
        console.error("File not loaded: "+file);
      return fs_cache[file];
    },
  };

  // List of files that the user can load into the editor.
  var mz_files = {
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

  // In case [corelib] and [stdlib] are not in the current directory.
  var src_dir = "";

  var ui = {

    // Write a message in the console.
    log: function (msg) {
      $("#console").append($("<div>").text(msg));
    },

    // Load a file in the editor.
    load: function (file) {
      fs.fetch(file, function (source) {
        editor.setValue(source);
        editor.clearSelection();
        editor.gotoLine(0);
      });
    },

    // The main driver for type-checking something.
    on_make: function (editor) {
      mezzo_ret_code = 0;
      try {
        var impl = mezzo.lex_and_parse_implementation(editor.getValue());
        mezzo.check_implementation(impl);
        if (mezzo_ret_code == 0) {
          ui.log("Successfully type-checked 😸");
        } else {
          ui.log("Mezzo terminated abruptly");
        }
      } catch (e) {
        ui.log("Error 😱 : "+e); 
      }
    },

    // Builds the left pane with the list of files that can be loaded into the
    // editor.
    build_explorer: function () {
      var list = $("#explorer ul");
      $.each(mz_files, function (folder, files) {
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

        var sublist = $("<ul>")
          .addClass("file-list");
        $.each(files, function (i, f) {
          var item = $("<li>");
          item.append($("<a href='#'></a>")
            .text(f)
            .click(function () {
              ui.load(folder+"/"+f);
            })
          );
          sublist.append(item);
        });
        item.append(sublist);
      });
      list.prepend($("<li>").append(
        $("<a href='#'>")
          .text("new")
          .click(function () {
            editor.setValue("");
          })));
    },

    // Setup the Ace editor.
    setup_editor: function () {
      editor = ace.edit("editor");
      editor.setTheme("ace/theme/chrome");
      editor.getSession().setMode("ace/mode/ocaml");

      editor.commands.addCommand({
        name: 'make',
        bindKey: {win: 'Ctrl-M',  mac: 'Command-M'},
        exec: ui.on_make,
        readOnly: true
      });
    },

  };

  // These functions are called from the OCaml side!
  mezzo_fs_get = fs.get;
  mezzo_ui_log = ui.log;

  $(document).ready(function () {
    ui.build_explorer();
    ui.setup_editor();

    ui.log("Editor successfully loaded, hit Ctrl-M or Command-M.");
  });

})();
