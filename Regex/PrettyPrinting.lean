-- import Regex.EREMatchSemantics
-- import Init.Data.List.Basic

-- variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

-- open BA ERE List TTerm

-- instance : ToString (BA Char) where
--   toString c := toStringBA c
--   where
--     toStringBA : BA Char → String
--     | atom a => a.repr
--     | top => "⊤"
--     | bot => "⊥"
--     | BA.and a b => toStringBA a ++ " ∧ " ++ toStringBA b
--     | BA.or a b => toStringBA a ++ " ∨ " ++ toStringBA b
--     | BA.not a => "¬ " ++ toStringBA a

-- instance : ToString (ERE (BA Char)) where
--   toString r := toStringRE r
--   where
--     toStringRE : ERE (BA Char) → String
--     | ε       => "ε"
--     | Pred a  => toString a
--     | r1 ⋓ r2 => "(" ++ toStringRE r1 ++ " + " ++ toStringRE r2 ++ ")"
--     | r1 ⋒ r2 => "(" ++ toStringRE r1 ++ " & " ++ toStringRE r2 ++ ")"
--     | r1 ⬝ r2 => "(" ++ toStringRE r1 ++  "⬝" ++ toStringRE r2 ++ ")"
--     | ~ r   => "~" ++ toStringRE r
--     | r *     => toStringRE r ++ "*"
--     | r1 : r2 => "(" ++ toStringRE r1 ++ " : " ++ toStringRE r2 ++ ")"

-- def addBranch (empty : Bool) (l : (String × List String)) : List String :=
--   match l with
--   | (_,[]) => []
--   | (n,x::xs) =>
--     let header := s!"+--{n}--";
--     (header ++ x) :: xs.map ((if empty then " " else "|") ++ String.replicate (header.length - 1) ' ' ++ ·)

-- def ppTree (head : String) (l : List (String × List String)) : List String :=
--   match l with
--   | [] => [head]
--   | x::xs => head :: "|" :: List.join ((x::xs).dropLast.map (addBranch false)) ++ addBranch true (x::xs).getLast!

-- def ppTreeNameless (head : String) (l : List (List String)) : List String :=
--   ppTree head (l.map ("", ·))

-- def ppTR' : TTerm (BA Char) (ERE (BA Char)) → List String
--   | Leaf r     => [toString r]
--   | Node c f g => ppTree ("ite(" ++ toString c ++ ")") [("fst", ppTR' f), ("snd", ppTR' g)]

-- -- Just concat the result
-- def ppTR (r : TTerm (BA Char) (ERE (BA Char))) : IO Unit :=
--   -- "\n" is the separator string
--   IO.print $ intersperse "\n" $ ppTR' r

-- /-- Elementary denotation predicates for (Unicode) characters. -/
-- instance : Denotation Char Char where
--   denote a b := a == b

-- /-- Helper function to convert strings into regexp literals (string as a sequence of characters) -/
-- def String.toRE (s : String) : ERE (BA Char) :=
--   s.toList |>.map (Pred ∘ BA.atom) |>.foldr (· ⬝ ·) ε

-- /-- Implicit coercion to convert strings to regexp to make them more readable. -/
-- instance : Coe String (ERE (BA Char)) where
--   coe := String.toRE

-- /-- Helper function to obtain a string as character class. -/
-- def String.characterClass (s : String) : BA Char :=
--   s.toList |>.map .atom |>.foldr .or .bot

-- def ab : ERE (BA Char) := (Pred (atom 'a')) ⬝ (Pred (atom 'b'))
-- def der_ab : TTerm (BA Char) (ERE (BA Char)) :=
--   derivative ab

-- #eval ppTR der_ab
-- #eval ppTR (derivative (ε ⬝ (Pred (atom 'b'))))
