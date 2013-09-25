/**
 * Takes the <b>entire</b> query string and returns an object whose keys are the
 * parameter names and values are corresponding values.
 * @param aStr The entire query string
 * @return An object that holds the decoded data
 */
function decodeUrlParameters(aStr) {
  let params = {};
  let i = aStr.indexOf("?");
  if (i >= 0) {
    let query = aStr.substring(i+1, aStr.length);
    let keyVals = query.split("&");
    for each (let [, keyVal] in Iterator(keyVals)) {
      let [key, val] = keyVal.split("=");
      val = decodeURIComponent(val);
      params[key] = val;
    }
  }
  return params;
}

/**
 * Python-style range function to use in list comprehensions.
 *  @param {Number} begin
 *  @param {Number} end
 *  @return {Iterator} An iterator that yields from begin to end - 1.
 */
function range(begin, end) {
  for (let i = begin; i < end; ++i) {
    yield i;
  }
}
