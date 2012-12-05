var texts = new Array();
var states = new Array();

texts['fold000001'] = '<a href="javascript:fold(\'fold000001\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 1 to line 53</i>';
states['fold000001'] = false;
texts['fold000060'] = '<a href="javascript:fold(\'fold000060\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 60 to line 78</i>';
states['fold000060'] = false;
texts['fold000080'] = '<a href="javascript:fold(\'fold000080\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 80 to line 91</i>';
states['fold000080'] = false;
texts['fold000099'] = '<a href="javascript:fold(\'fold000099\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 99 to line 99</i>';
states['fold000099'] = false;
texts['fold000101'] = '<a href="javascript:fold(\'fold000101\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 101 to line 101</i>';
states['fold000101'] = false;
texts['fold000103'] = '<a href="javascript:fold(\'fold000103\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 103 to line 105</i>';
states['fold000103'] = false;
texts['fold000107'] = '<a href="javascript:fold(\'fold000107\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 107 to line 121</i>';
states['fold000107'] = false;
texts['fold000123'] = '<a href="javascript:fold(\'fold000123\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 123 to line 133</i>';
states['fold000123'] = false;
texts['fold000135'] = '<a href="javascript:fold(\'fold000135\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 135 to line 140</i>';
states['fold000135'] = false;
texts['fold000142'] = '<a href="javascript:fold(\'fold000142\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 142 to line 151</i>';
states['fold000142'] = false;
texts['fold000153'] = '<a href="javascript:fold(\'fold000153\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 153 to line 153</i>';
states['fold000153'] = false;
texts['fold000155'] = '<a href="javascript:fold(\'fold000155\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 155 to line 159</i>';
states['fold000155'] = false;
texts['fold000161'] = '<a href="javascript:fold(\'fold000161\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 161 to line 164</i>';
states['fold000161'] = false;
texts['fold000166'] = '<a href="javascript:fold(\'fold000166\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 166 to line 166</i>';
states['fold000166'] = false;
texts['fold000168'] = '<a href="javascript:fold(\'fold000168\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 168 to line 168</i>';
states['fold000168'] = false;
texts['fold000170'] = '<a href="javascript:fold(\'fold000170\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 170 to line 170</i>';
states['fold000170'] = false;
texts['fold000172'] = '<a href="javascript:fold(\'fold000172\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 172 to line 174</i>';
states['fold000172'] = false;

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
