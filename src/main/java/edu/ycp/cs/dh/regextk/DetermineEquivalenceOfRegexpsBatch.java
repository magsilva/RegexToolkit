// RegexToolkit - A Java library for regular expressions and finite automata
// Copyright (C) 2013,2014,2017 David H. Hovemeyer <david.hovemeyer@gmail.com>
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files (the
// "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to whom the Software is furnished to do so, subject to
// the following conditions:
// 
// The above copyright notice and this permission notice shall be included
// in all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
// TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
// SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

package edu.ycp.cs.dh.regextk;

import java.util.Scanner;

/**
 * Check a batch of regular expressions to see whether each
 * is or isn't equivalent to a master regular expression.
 * Useful for grading.
 * 
 * @author David Hovemeyer
 */
public class DetermineEquivalenceOfRegexpsBatch {
	public static void main(String[] args) {
		@SuppressWarnings("resource")
		Scanner keyboard = new Scanner(System.in);

		System.out.print("Master regexp: ");
		String master = keyboard.nextLine();
		
		while (keyboard.hasNextLine()) {
			String r = keyboard.nextLine();
			if (r == null) {
				break;
			}
			
			DetermineEquivalenceOfRegexps.compareRegexps(master, r, "Master", "R");
		}
	}
}
