/*****************************************************************************/
/*  Mezzo, a programming language based on permissions                       */
/*  Copyright (C) 2011, 2012 Jonathan Protzenko and François Pottier         */
/*                                                                           */
/*  This program is free software: you can redistribute it and/or modify     */
/*  it under the terms of the GNU General Public License as published by     */
/*  the Free Software Foundation, either version 3 of the License, or        */
/*  (at your option) any later version.                                      */
/*                                                                           */
/*  This program is distributed in the hope that it will be useful,          */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of           */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            */
/*  GNU General Public License for more details.                             */
/*                                                                           */
/*  You should have received a copy of the GNU General Public License        */
/*  along with this program.  If not, see <http://www.gnu.org/licenses/>.    */
/*                                                                           */
/*****************************************************************************/

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
