var texts = new Array();
var states = new Array();

texts['fold000001'] = '<a href="javascript:fold(\'fold000001\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 1 to line 53</i>';
states['fold000001'] = false;
texts['fold000055'] = '<a href="javascript:fold(\'fold000055\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 55 to line 67</i>';
states['fold000055'] = false;
texts['fold000069'] = '<a href="javascript:fold(\'fold000069\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 69 to line 79</i>';
states['fold000069'] = false;
texts['fold000081'] = '<a href="javascript:fold(\'fold000081\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 81 to line 92</i>';
states['fold000081'] = false;
texts['fold000094'] = '<a href="javascript:fold(\'fold000094\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 94 to line 96</i>';
states['fold000094'] = false;
texts['fold000098'] = '<a href="javascript:fold(\'fold000098\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 98 to line 147</i>';
states['fold000098'] = false;
texts['fold000149'] = '<a href="javascript:fold(\'fold000149\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 149 to line 153</i>';
states['fold000149'] = false;
texts['fold000155'] = '<a href="javascript:fold(\'fold000155\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 155 to line 188</i>';
states['fold000155'] = false;
texts['fold000190'] = '<a href="javascript:fold(\'fold000190\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 190 to line 194</i>';
states['fold000190'] = false;
texts['fold000196'] = '<a href="javascript:fold(\'fold000196\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 196 to line 253</i>';
states['fold000196'] = false;
texts['fold000255'] = '<a href="javascript:fold(\'fold000255\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 255 to line 298</i>';
states['fold000255'] = false;

function fold(id) {
  tmp = document.getElementById(id).innerHTML;
  document.getElementById(id).innerHTML = texts[id];
  texts[id] = tmp;
  states[id] = !(states[id]);
}

function unfoldAll() {
  for (key in states) {
    if (states[key]) {
      fold(key);
    }
  }
}

function foldAll() {
  for (key in states) {
    if (!(states[key])) {
      fold(key);
    }
  }
}
