"use strict";

(function ($) {
  var mkString = function (str, count) {
    var arr = [];
    arr.length = (count + 1);
    return arr.join(str);
  };

  $.fn.mezzoAnimate = function (arg) {

    var currentSeqNo;

    // V8 welcomes you to the stone age! http://code.google.com/p/v8/issues/detail?id=811
    var data = arg.data,
        offset = arg.options.offset,
        prev = arg.prev,
        next = arg.next,
        dup = arg.dup,
        nondup = arg.nondup;

    var indexAndLineForSeqNo = function (seqNo) {
      if (seqNo == 0)
        return [0, offset];

      var line = 0;
      var i = 0;
      var currSeqNo = 0;
      
      while (i < data.length - 1) {
        i++;
        switch (data[i].special) {
          case "skip":
            line++;
            break;

          case "hold":
            currSeqNo++;
            break;

          default:
            line++;
            currSeqNo++;
        }
        if (currSeqNo == seqNo)
          break;
      }

      if (i < data.length)
        return [i, line+offset];
      else
        console.error("Nothing for this sequence number");
    };

    var fillBoxes = function (index) {
      // Now [index] is the real index in the [data] array.
      var fill = function (box, items) {
        var i, list;
        list = $("<ul />").addClass("mezzoList");
        box.empty();
        box.append(list);
        for (i = 0; i < items.length; ++i) {
          list.append(
            $("<li />").append(
              $("<code />").text(items[i])
            )
          );
        }
      };
      fill($(dup), data[index].left);
      fill($(nondup), data[index].right);
    };

    var mezzoGo = function (seqNo) {
      var indexLine = indexAndLineForSeqNo(seqNo);
      if (indexLine) {
        // Remember the current sequence number
        currentSeqNo = seqNo;

        // Hate you V8!
        var index = indexLine[0],
            line  = indexLine[1];
        // var [index, line] = indexLine;

        // Fill the whitespace-holder accordingly
        var fill = this.find(".mezzoFill");
        if (line == 0)
          fill.empty();
        else
          fill.text(mkString("\n", line));

        fillBoxes(index);
      }
    };

    var parent, overlay, arrow, fill, self;

    self = this;

    // Safety check
    if (!this.is("pre"))
      console.log("[mezzoAnimate]: please call me on <pre> elements");

    // Enclose in another <div>
    this.wrap('<div class="mezzoAnimate" />');
    parent = this.parent();
    parent.css("height", parent.height());

    // Create the overlay by copying the original element.
    overlay = $("<div />")
      .appendTo(parent)
      .addClass("mezzoOverlay");

    // Create the fill
    fill = $("<pre />")
      .addClass("mezzoFill")
      .appendTo(overlay);

    // Create the arrow
    arrow = $("<div />")
      .addClass("mezzoArrow")
      .appendTo(overlay);

    // Add the class now so that it doesn't get cloned too.
    this.addClass("mezzoCode");

    mezzoGo.call(this.closest(".mezzoAnimate"), 0);

    $(prev).click(function (event) {
      mezzoGo.call(self.closest(".mezzoAnimate"), Math.max(0, currentSeqNo - 1));
      event.preventDefault();
    });

    $(next).click(function (event) {
      mezzoGo.call(self.closest(".mezzoAnimate"), currentSeqNo + 1);
      event.preventDefault();
    });
  };
})(jQuery);
