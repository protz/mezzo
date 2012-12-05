var texts = new Array();
var states = new Array();

texts['fold000001'] = '<a href="javascript:fold(\'fold000001\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 1 to line 90</i>';
states['fold000001'] = false;
texts['fold000092'] = '<a href="javascript:fold(\'fold000092\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 92 to line 113</i>';
states['fold000092'] = false;
texts['fold000115'] = '<a href="javascript:fold(\'fold000115\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 115 to line 131</i>';
states['fold000115'] = false;
texts['fold000136'] = '<a href="javascript:fold(\'fold000136\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 136 to line 137</i>';
states['fold000136'] = false;
texts['fold000140'] = '<a href="javascript:fold(\'fold000140\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 140 to line 141</i>';
states['fold000140'] = false;
texts['fold000144'] = '<a href="javascript:fold(\'fold000144\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 144 to line 146</i>';
states['fold000144'] = false;
texts['fold000148'] = '<a href="javascript:fold(\'fold000148\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 148 to line 156</i>';
states['fold000148'] = false;

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
