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

(ns tools.compiler.grammar
  (:require [clojure.set :as cset])
  (:require [clojure.core.match :refer [match]])
  (:require [clojure.string :as cstr])
  (:require [clostache.parser :refer [render-resource]])
  (:require [clojure.math.combinatorics :as combo])
  )

(declare compute-first-sets)

(defn setGrammar [g]
  (def grammar g)
  (def sigma (grammar 'sigma))
  (def S (grammar 'S))
  (def P (grammar 'P))
  (def N (cset/difference
           (set (flatten [(keys P) (vals P)]))
           (grammar 'sigma)))
  (def
    ^{:doc "All symbols"}
    alls (cset/union sigma N))
  (def

    ^{:doc "For each non-terminal symbol, it's FIRST set"}
    first-sets (into {}
                 ; init
                 (for [e alls]
                   [e (if (sigma e)
                        (atom #{e})
                        (atom #{}))
                    ])))

  (def
    ^{:doc "For each non-terminal symbol, it's FOLLOW set"}
    follow-sets (into {}
                  ; init
                  (for [e N]
                    [e (if (= S e)
                         ; Regla 1
                         (atom #{'eot})
                         (atom #{}))
                     ])))
  (def flag-first false)
  (def flag-follow false)
  )

(defn-
  ^{:doc "Total size of FIRST (or FOLLOW) sets"
    :arglists '([d])}
  count-dict [d] (reduce + (for [[_ ys] d]
                             (count @ys))))

(defn
  ^{:doc "Compute the FIRST set from a string of symbols:
          FIRST(X_1 X_2 ... X_n)"
    :arglists '([lstr])}
  first-set-str [lstr]
  (when-not flag-first
    (compute-first-sets))
  (let [res (atom #{})]
    (loop [l lstr]
      (match [l]
        [[]] (swap! res
               #(cset/union % %2)
                 #{'e})
        [[h & t]] (let [hfirst-set @(first-sets h)]
                    (swap! res
                      #(cset/union % %2)
                      (cset/difference hfirst-set #{'e})
                      )
                    (when (hfirst-set 'e)
                      (recur t)
                      ))))
    @res)
  )

(defn-
  ^{:doc "Calculate the first sets"
    :arglists '([])}
  compute-first-sets []
  (def flag-first true)
  (loop [cant (count-dict first-sets)]
    ; x -> partes izquierdas (no terminal)
    ; ys -> secuencia de partes derechas (pd),
    ; pd -> secuencia de símbolos de la parte derecha correspondiente
    (doseq [[x ys] P]
      (doseq [yss ys] ; Para cada parte derecha (yss) de un no terminal dado
        (loop [l yss]
          (match [l]
            ; $\epsilon$ es parte de FRIST(X) cuando X derive $\epsilon$
            ; o cuando todos los Y_i lo hayan hecho
            [[]] (swap! (first-sets x)
                   #(cset/union % %2)
                     #{'e})
            ; En cada Y_i (h) cuando sus anteriores derivan $\epsilon$
            [[h & t]] (let [hfirst-set @(first-sets h)]
                        (swap! (first-sets x)
                          ; Añadir a FIRST(X) el resultado de: (FIRST(Y_i) - $\epsilon$)
                          #(cset/union % %2)
                          (cset/difference hfirst-set #{'e}))
                        ; Si FIRST(Y_i) incluye a $\epsilon$ entonces
                        ; se siguen buscando símbolos
                        (when (hfirst-set 'e)
                          (recur t)
                          ))))))
    (let [fcant (count-dict first-sets)]
      (when-not (= cant fcant)
        (recur fcant)))))

(defn-
  ^{:doc "Calculate the follow sets"
    :arglists '([])}
  compute-follow-sets []
  (def flag-follow true)
  (loop [cant (count-dict follow-sets)]
    (doseq [[x ys] P]
      (doseq [yss ys :when (not= yss [])]
        (loop [l yss]
          (if (N (first l))
            (match [l]
              ; Regla 3
              [[h & []]] (swap! (follow-sets h)
                           #(cset/union % %2)
                           @(follow-sets x))

              [[h & t]] (let [first-set-t (first-set-str t)]
                          ; Regla 2
                          (swap! (follow-sets h)
                            #(cset/union % %2)
                            (cset/difference first-set-t #{'e}))
                          ; Regla 3
                          (when (first-set-t 'e)
                            (swap! (follow-sets h)
                              #(cset/union % %2)
                              @(follow-sets x)))
                          (recur t)))
            (when (seq l) ; Solamente para no terminales
              (recur (subvec l 1)))))))

    (let [fcant (count-dict follow-sets)]
      (when-not (= cant fcant)
        (recur fcant)))))

(defn get-first-sets []
  (when-not flag-first
    (compute-first-sets))
  (into {} (for [[x ys] first-sets] [x @ys]))
  )

(defn get-follow-sets []
  (when-not flag-first
    (compute-first-sets))
  (when-not flag-follow
    (compute-follow-sets))
  (into {} (for [[x ys] follow-sets] [x @ys]))
  )

(defn- LL1-prop? [[A [alpha beta]]]
  ; Para: A -> alpha | beta
  ; 1. first(alpha) disjunto first(beta)
  ; 2. a lo sumo, uno de first(alpha) o first(beta) puede tener e
  ;       - Nota: caso particular del punto 1
  ; 3. cuando beta derive e:  first(alpha) disjunto follow(A)

  (let [
         follow-sets (get-follow-sets)
         cond1 #(empty? (cset/intersection
                          (first-set-str alpha)
                          (first-set-str beta)))

         derive-e? (fn [pder]
                     (some #{'e} (first-set-str pder)))

         cond3 #(cond
                  (derive-e? alpha) (empty? (cset/intersection
                                              (first-set-str beta)
                                              (follow-sets A)))

                  (derive-e? beta) (empty? (cset/intersection
                                             (first-set-str alpha)
                                             (follow-sets A)))
                  :else true
                  )
         ]
    (and (cond1) (cond3))
    ))

(defn
  ^{
     ;     :doc "Returns {:result true} when the grammar is LL1 or
     ;         {:result false :reason <reason>} if not."
     :doc "Returns if the grammar is LL1 or not."
     :arglists '([])
     }
  LL1? []
  (let [
         p-with-size_>_1 (for [[k v] P
                               :when (> (count v) 1)]
                           k)
         combinations (for [no-terminal p-with-size_>_1]
                        (for [cmb (combo/combinations (P no-terminal) 2)]
                          [no-terminal (vec cmb)]))
         ]
    (nil? (first (for [c combinations
                       :when (not (LL1-prop? (first c)))]
                   c
                   )))
    ))

(defn LL1-parser-firsts []
  (into {} (for [[k vs] P]
             (let [rprod-frsts (for [vi vs :when (not= vi [])]
                                 [vi (first-set-str vi)])]

               [k
                [
                  (for [[i elem] (map-indexed vector
                                   rprod-frsts)]
                    [elem (inc i)]
                    )

                  (= (some #{[]} vs) [])
                  ]
                ]
               ))))


(defn get-LL1-parser-java-memo []
  (let [
         fs (LL1-parser-firsts)

         first-sets-values (flatten (for [[k [vs _]] fs]
                                      (for [[vis i] vs]
                                        {
                                          :name (str k i)
                                          :tokens (cstr/join ", " (nth vis 1))
                                          }
                                        )))

         productions (for [[k [values epsilon]] fs]
                       {
                         :epsilon epsilon
                         :name k
                         :rightParts (cstr/join " | " (map #(cstr/join " " %) (P k)))
                         :firsts (for [[vi i] values]
                                   {
                                     :i i
                                     :symbols (for [symbol_i (nth vi 0)]
                                                {
                                                  :name symbol_i
                                                  :is-token (sigma symbol_i)
                                                  }
                                                )
                                     }
                                   )

                         :firsts-values (cstr/join ", "
                                          (for [[_ i] values]
                                            (str "first" k i)))
                         }
                       )
         ]

    (render-resource "templates/parser.mustache"
      (into (grammar 'config) {
                                :first-sets-values first-sets-values
                                :S S
                                :productions productions
                                }))

    )
  )
