module Lattice

type Lattice<'a when 'a : comparison> = Set<'a> * Set<'a> * Set<'a> -> Set<'a> -> Set<'a> ;;

let btm (b,t,o) = b ;;
let top (b,t,o) = t ;;
let lob s1 s2 (b,t,o) = o s1 s2 ;;
let subeq s1 s2 (b,t,o) = (o s1 s2 ) = s2 ;;
let supeq s1 s2 (b,t,o) = (o s1 s2 ) = s1 ;;
let sup s1 s2 L = not (subeq s1 s2 L)
let sub s1 s2 L = not (supeq s1 s2 L)
