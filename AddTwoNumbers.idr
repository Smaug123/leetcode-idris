module AddTwoNumbers

data Digit = D Int

ofIntHelp : Int -> List Digit
ofIntHelp 0 = []
ofIntHelp i = D (i `mod` 10) :: ofIntHelp (i `div` 10)

ofInt : Int -> List Digit
ofInt 0 = [D 0]
ofInt i = ofIntHelp i

addHelp : Bool -> List Digit -> List Digit -> List Digit
addHelp carry [] [] = if carry then [D 1] else []
addHelp False [] ys = ys
addHelp True [] ys = addHelp False [D 1] ys
addHelp False xs [] = xs
addHelp True xs [] = addHelp False [D 1] xs
addHelp carry (D x :: xs) (D y :: ys) =
  let sum = x + y + if carry then 1 else 0 in
  if sum >= 10 then
    D (sum `mod` 10) :: addHelp True xs ys
  else
    D sum :: addHelp False xs ys

add : List Digit -> List Digit -> List Digit
add = addHelp False

test1 : add (ofInt 342) (ofInt 465) = ofInt 807
test1 = Refl
test2 : add [D 0] [D 0] = [D 0]
test2 = Refl
test3 : add (map D [9,9,9,9,9,9,9]) (map D [9,9,9,9]) = map D [8,9,9,9,0,0,0,1]
test3 = Refl
