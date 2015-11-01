;;
;; Author José Albert Cruz Almaguer <jalbertcruz@gmail.com>
;; Copyright 2015 by José Albert Cruz Almaguer.
;;
;; This program is licensed to you under the terms of version 3 of the
;; GNU Affero General Public License. This program is distributed WITHOUT
;; ANY EXPRESS OR IMPLIED WARRANTY, INCLUDING THOSE OF NON-INFRINGEMENT,
;; MERCHANTABILITY OR FITNESS FOR A PARTICULAR PURPOSE. Please refer to the
;; AGPL (http://www.gnu.org/licenses/agpl-3.0.txt) for more details.
;;

(ns tools.compiler.lexer
  (:require [clojure.string :as cstr])
  )

(def tkns-desc-init '[
                       [space "[\t \n]+"]
                       ])

(declare tkns-desc tkns)

(defn setTokens-desc [descs]
  (def tkns-desc (apply conj tkns-desc-init descs))
  (def tkns (map (fn [[name pattern]]
                   [name (re-pattern (str "^" pattern))]) tkns-desc))
  )

(def tab-size 3)

(defn all-tokens-in-str [ln]
  (loop [cln (cstr/replace ln #"\r" "") res [] row 1 col 1]
    (let [primero (first (filter #(re-find (% 1) cln) tkns))]
      (if (seq primero)
        (let [lex (re-find (primero 1) cln)]
          (if (= (primero 0) 'space)
            (let [
                   nrow (+ row (count (filter #(= % \newline) lex)))
                   [col-init text-2-count] (if (= nrow row) ; si no hay \n
                                             [col lex]
                                             [1 (peek (cstr/split lex #"\n"))]
                                             )
                   ncol (reduce + col-init (map #(case %
                                                   \tab tab-size
                                                   \space 1
                                                   1) text-2-count))
                   ]
              (recur (.substring cln (count lex)) (conj res [(primero 0) lex row col]) nrow ncol))
            (recur (.substring cln (count lex)) (conj res [(primero 0) lex row col]) row (+ col (count lex)))))
        (if (seq cln)
          (recur (.substring cln 1) (conj res ['error (.substring cln 0 1) row col]) row (inc col))
          (conj res ['eot nil row col]))))))

(defn tokens-in-str [ln]
  (for [[tk lex r c] (all-tokens-in-str ln) :when (not= tk 'space)] [tk lex r c]))
