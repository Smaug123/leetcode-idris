module LongestNonRepeatingSubstring

Set : Type -> Type
Set = List

contains : Eq a => a -> Set a -> Bool
contains x [] = False
contains x (y :: ys) = (x == y) || contains x ys

add : a -> Set a -> Set a
add x xs = x :: xs

emptySet : {0 a : Type} -> Set a
emptySet = []

longestHelp : {0 a : Type} -> Eq a => Set a -> Int -> Int -> List a -> Int
longestHelp seen count soFar [] = max soFar count
longestHelp seen count soFar (x :: xs) =
  if contains x seen then longestHelp (emptySet {a}) 0 (max soFar count) (x :: xs) else
  longestHelp (add x seen) (count + 1) soFar xs

longest : Eq a => List a -> Int
longest = longestHelp (emptySet {a}) 0 0

test1 : longest (unpack "abcabcbb") = 3
test1 = Refl
test2 : longest (unpack "bbbbb") = 1
test2 = Refl
test3 : longest (unpack "pwwkew") = 3
test3 = Refl
test4 : longest (unpack "") = 0
test4 = Refl
