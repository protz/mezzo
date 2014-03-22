var mezzo_fs;
var mezzo_ui_log;
var mezzo_ui_log_char;
var mezzo_ret_code;
var mezzo_toplevel_filename = "::toplevel.mz";
var mezzo_toplevel_filename_i = "::toplevel.mzi";

(function () {
  "use strict";

  // The Ace editor.
  var editor;

  // A glue to hide the fact that there is no filesystem, only files that can be
  // fetched over http.
  var fs_cache = {};
  var fs = {
    normalize: function (file) {
      if (file.substr(0, 2) == "./")
        return fs.normalize(file.substring(2, file.length));
      else
        return file;
    },

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
          mimeType: "textPlain",
        });
      }
    },

    get: function(file) {
      console.log("get", file);
      file = fs.normalize(file);
      if (file == mezzo_toplevel_filename)
        return editor.getValue();
      else if (file == mezzo_toplevel_filename_i)
        // No interface for our toplevel
        return "";
      if (!(file in fs_cache))
        console.error("File not loaded: "+file);
      return fs_cache[file];
    },

    exists: function (file) {
      console.log("File exists?", file);
      file = fs.normalize(file);
      return (file == mezzo_toplevel_filename ||
              file == mezzo_toplevel_filename_i ||
              (file in fs_cache));
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

    "demos": [
      "demo-1.mz",
      "demo-2.mz",
      "demo-2-fixed.mz",
      "demo-3.mz",
      "demo-3-fix1.mz",
      "demo-3-fix2.mz",
      "demo-4.mz",
      "demo-5.mz",
      "demo-5-fix.mz",
    ],
   };

  // In case [corelib] and [stdlib] are not in the current directory.
  var src_dir = "";

  var ui = {

    // Write a message in the console.
    log: function (msg, isCamlOutput) {
      var console = $("#console");
      var buf = console.children().last();
      if (isCamlOutput && !buf.hasClass("char-buffer"))
        // This is an output from ocaml, make sure the last div is a proper
        // caml-buffer.
        buf = $("<div />")
          .addClass("char-buffer")
          .addClass("message")
          .appendTo(console);
      else if (!isCamlOutput)
        // This is a regular output, always create a new div.
        buf = $("<div />")
          .addClass("message")
          .appendTo(console);
      buf.text(buf.text()+msg);
      console.scrollTop(console.prop("scrollHeight"));
    },

    log_char: function (c) {
      ui.log(String.fromCharCode(c), true);
    },

    clear: function () {
      $("#console").empty();
    },

    // Write a timestamp in the console
    timestamp: function () {
      $("#console").append(
        $("<div>").addClass("timestamp").text(
          (new Date()).toLocaleTimeString()));
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
      ui.timestamp();
      mezzo_ret_code = 0;
      try {
        mezzo.process(
          new MlString(mezzo_toplevel_filename),
          $("#option-typecheck").prop("checked"),
          $("#option-interpret").prop("checked"),
          parseInt($("#option-debug").val()),
          new MlString($("#option-warnerror").val())
        );
        if (mezzo_ret_code == 0) {
          ui.log("Mezzo invocation successful 😸");
        } else {
          ui.log("Mezzo terminated abruptly");
        }
      } catch (e) {
        ui.log("Mezzo threw an Exception 😱 : "+e);
        ui.log("Mezzo threw an Exception 😱 : "+e);
        console.log(e.stack);
        throw e;
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

        if (folder == "corelib" || folder == "stdlib")
          item.find("a.toggle").click();
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

      editor.focus();
    },

  };

  var loader = {
    // Brutally load all files. Improve this.
    load_all: function () {
      var count = 1;
      var finish = function () {
        if (--count == 0) {
          ui.timestamp();
          ui.log("All files loaded");
        }
      };
      var grab = function (f) {
        count++;
        fs.fetch(f, finish);
      };
      ui.log("Loading files...");
      grab("corelib/autoload");
      finish();
      $.each(mz_files, function (dir, files) {
        $.each(files, function (i, f) {
          grab(dir + "/" + f);
        });
      });
    },
  };

  // These functions are called from the OCaml side!
  mezzo_fs = fs;
  mezzo_ui_log = ui.log;
  mezzo_ui_log_char = ui.log_char;

  $(document).ready(function () {
    // Register all event listeners + default values
    $("#command-clear").click(ui.clear);
    $("#command-go").click(ui.on_make);
    $("#option-typecheck").prop("checked", true);
    $("#option-warnerror").val("-1+2..4-5+6");
    $("#show-more-options").click(function () {
      $(this).next().show("slow");
      $(this).remove();
    });

    ui.timestamp();
    loader.load_all();

    ui.build_explorer();
    ui.setup_editor();

    ui.log("Editor successfully loaded, hit Ctrl-M or Command-M.");
  });

})();
