var texts = new Array();
var states = new Array();

texts['fold000001'] = '<a href="javascript:fold(\'fold000001\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 1 to line 64</i>';
states['fold000001'] = false;
texts['fold000066'] = '<a href="javascript:fold(\'fold000066\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 66 to line 104</i>';
states['fold000066'] = false;
texts['fold000106'] = '<a href="javascript:fold(\'fold000106\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 106 to line 106</i>';
states['fold000106'] = false;
texts['fold000108'] = '<a href="javascript:fold(\'fold000108\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 108 to line 108</i>';
states['fold000108'] = false;
texts['fold000112'] = '<a href="javascript:fold(\'fold000112\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 112 to line 112</i>';
states['fold000112'] = false;
texts['fold000114'] = '<a href="javascript:fold(\'fold000114\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 114 to line 153</i>';
states['fold000114'] = false;
texts['fold000155'] = '<a href="javascript:fold(\'fold000155\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 155 to line 167</i>';
states['fold000155'] = false;
texts['fold000170'] = '<a href="javascript:fold(\'fold000170\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 170 to line 181</i>';
states['fold000170'] = false;
texts['fold000183'] = '<a href="javascript:fold(\'fold000183\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 183 to line 208</i>';
states['fold000183'] = false;
texts['fold000210'] = '<a href="javascript:fold(\'fold000210\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 210 to line 239</i>';
states['fold000210'] = false;
texts['fold000241'] = '<a href="javascript:fold(\'fold000241\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 241 to line 286</i>';
states['fold000241'] = false;
texts['fold000288'] = '<a href="javascript:fold(\'fold000288\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 288 to line 298</i>';
states['fold000288'] = false;
texts['fold000300'] = '<a href="javascript:fold(\'fold000300\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 300 to line 324</i>';
states['fold000300'] = false;
texts['fold000327'] = '<a href="javascript:fold(\'fold000327\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 327 to line 327</i>';
states['fold000327'] = false;
texts['fold000331'] = '<a href="javascript:fold(\'fold000331\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 331 to line 418</i>';
states['fold000331'] = false;
texts['fold000420'] = '<a href="javascript:fold(\'fold000420\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 420 to line 422</i>';
states['fold000420'] = false;
texts['fold000425'] = '<a href="javascript:fold(\'fold000425\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 425 to line 543</i>';
states['fold000425'] = false;
texts['fold000545'] = '<a href="javascript:fold(\'fold000545\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 545 to line 576</i>';
states['fold000545'] = false;
texts['fold000578'] = '<a href="javascript:fold(\'fold000578\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 578 to line 693</i>';
states['fold000578'] = false;
texts['fold000695'] = '<a href="javascript:fold(\'fold000695\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 695 to line 754</i>';
states['fold000695'] = false;
texts['fold000757'] = '<a href="javascript:fold(\'fold000757\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 757 to line 815</i>';
states['fold000757'] = false;
texts['fold000817'] = '<a href="javascript:fold(\'fold000817\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 817 to line 859</i>';
states['fold000817'] = false;
texts['fold000861'] = '<a href="javascript:fold(\'fold000861\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 861 to line 883</i>';
states['fold000861'] = false;

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
