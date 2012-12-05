var texts = new Array();
var states = new Array();

texts['fold000001'] = '<a href="javascript:fold(\'fold000001\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 1 to line 104</i>';
states['fold000001'] = false;
texts['fold000106'] = '<a href="javascript:fold(\'fold000106\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 106 to line 106</i>';
states['fold000106'] = false;
texts['fold000108'] = '<a href="javascript:fold(\'fold000108\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 108 to line 114</i>';
states['fold000108'] = false;
texts['fold000116'] = '<a href="javascript:fold(\'fold000116\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 116 to line 127</i>';
states['fold000116'] = false;
texts['fold000129'] = '<a href="javascript:fold(\'fold000129\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 129 to line 129</i>';
states['fold000129'] = false;
texts['fold000131'] = '<a href="javascript:fold(\'fold000131\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 131 to line 136</i>';
states['fold000131'] = false;
texts['fold000138'] = '<a href="javascript:fold(\'fold000138\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 138 to line 281</i>';
states['fold000138'] = false;

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
