var texts = new Array();
var states = new Array();

texts['fold000001'] = '<a href="javascript:fold(\'fold000001\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 1 to line 80</i>';
states['fold000001'] = false;
texts['fold000083'] = '<a href="javascript:fold(\'fold000083\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 83 to line 83</i>';
states['fold000083'] = false;
texts['fold000085'] = '<a href="javascript:fold(\'fold000085\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 85 to line 86</i>';
states['fold000085'] = false;
texts['fold000088'] = '<a href="javascript:fold(\'fold000088\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 88 to line 89</i>';
states['fold000088'] = false;
texts['fold000091'] = '<a href="javascript:fold(\'fold000091\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 91 to line 92</i>';
states['fold000091'] = false;
texts['fold000094'] = '<a href="javascript:fold(\'fold000094\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 94 to line 110</i>';
states['fold000094'] = false;
texts['fold000112'] = '<a href="javascript:fold(\'fold000112\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 112 to line 113</i>';
states['fold000112'] = false;
texts['fold000115'] = '<a href="javascript:fold(\'fold000115\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 115 to line 117</i>';
states['fold000115'] = false;

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
