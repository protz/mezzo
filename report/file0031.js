var texts = new Array();
var states = new Array();

texts['fold000001'] = '<a href="javascript:fold(\'fold000001\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 1 to line 57</i>';
states['fold000001'] = false;
texts['fold000059'] = '<a href="javascript:fold(\'fold000059\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 59 to line 96</i>';
states['fold000059'] = false;
texts['fold000098'] = '<a href="javascript:fold(\'fold000098\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 98 to line 144</i>';
states['fold000098'] = false;
texts['fold000146'] = '<a href="javascript:fold(\'fold000146\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 146 to line 179</i>';
states['fold000146'] = false;
texts['fold000182'] = '<a href="javascript:fold(\'fold000182\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 182 to line 187</i>';
states['fold000182'] = false;
texts['fold000189'] = '<a href="javascript:fold(\'fold000189\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 189 to line 198</i>';
states['fold000189'] = false;
texts['fold000200'] = '<a href="javascript:fold(\'fold000200\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 200 to line 202</i>';
states['fold000200'] = false;
texts['fold000205'] = '<a href="javascript:fold(\'fold000205\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 205 to line 208</i>';
states['fold000205'] = false;
texts['fold000210'] = '<a href="javascript:fold(\'fold000210\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 210 to line 213</i>';
states['fold000210'] = false;
texts['fold000215'] = '<a href="javascript:fold(\'fold000215\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 215 to line 218</i>';
states['fold000215'] = false;
texts['fold000220'] = '<a href="javascript:fold(\'fold000220\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 220 to line 220</i>';
states['fold000220'] = false;
texts['fold000222'] = '<a href="javascript:fold(\'fold000222\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 222 to line 223</i>';
states['fold000222'] = false;
texts['fold000225'] = '<a href="javascript:fold(\'fold000225\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 225 to line 225</i>';
states['fold000225'] = false;
texts['fold000227'] = '<a href="javascript:fold(\'fold000227\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 227 to line 236</i>';
states['fold000227'] = false;
texts['fold000238'] = '<a href="javascript:fold(\'fold000238\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 238 to line 244</i>';
states['fold000238'] = false;

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
