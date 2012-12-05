var texts = new Array();
var states = new Array();

texts['fold000001'] = '<a href="javascript:fold(\'fold000001\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 1 to line 22</i>';
states['fold000001'] = false;
texts['fold000024'] = '<a href="javascript:fold(\'fold000024\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 24 to line 29</i>';
states['fold000024'] = false;
texts['fold000031'] = '<a href="javascript:fold(\'fold000031\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 31 to line 43</i>';
states['fold000031'] = false;
texts['fold000045'] = '<a href="javascript:fold(\'fold000045\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 45 to line 47</i>';
states['fold000045'] = false;
texts['fold000049'] = '<a href="javascript:fold(\'fold000049\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 49 to line 51</i>';
states['fold000049'] = false;
texts['fold000053'] = '<a href="javascript:fold(\'fold000053\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 53 to line 55</i>';
states['fold000053'] = false;
texts['fold000057'] = '<a href="javascript:fold(\'fold000057\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 57 to line 59</i>';
states['fold000057'] = false;
texts['fold000061'] = '<a href="javascript:fold(\'fold000061\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 61 to line 64</i>';
states['fold000061'] = false;
texts['fold000066'] = '<a href="javascript:fold(\'fold000066\');"><img border="0" height="10" width="10" src="plus.png" title="unfold code"/></a><i>&nbsp;&nbsp;code folded from line 66 to line 78</i>';
states['fold000066'] = false;

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
