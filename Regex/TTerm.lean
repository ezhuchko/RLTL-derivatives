import Regex.Definitions

/-!
# Transition terms

Collection of all definitions and lemmas about transition terms.

-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ] [DecidableEq α]

/-- Transition terms where α is the type of the alphabet and
    β is the type of leaves which represents the language of the automata. -/
inductive TTerm (α β : Type) : Type where
  | Leaf : β → TTerm α β
  | Node (condition : α) (_then : TTerm α β) (_else : TTerm α β) : TTerm α β
  deriving Repr, DecidableEq
open TTerm

-- monad identity
@[simp]
def TTerm.pure (b : β) : TTerm α β := TTerm.Leaf b

-- monad multiplication
def TTerm.join (b : TTerm α (TTerm α β)) : TTerm α β :=
  match b with
  | Leaf b => b
  | Node p f g => Node p (join f) (join g)

@[simp]
def TTerm.fmap {β γ : Type} (f : β → γ) (b : TTerm α β) : TTerm α γ :=
  match b with
  | Leaf b => pure (f b)
  | Node p a b => Node p (fmap f a) (fmap f b)

@[simp]
def TTerm.bind {β γ : Type} (f : β → TTerm α γ) : TTerm α β → TTerm α γ :=
  fun b => join (fmap f b)

instance {α : Type} : Monad (TTerm α) where
  pure {β : Type} (b : β) := pure b
  bind q e := join (fmap e q)

def lift_unary (op : β → β') (g : TTerm α β) : TTerm α β' := fmap op g

def lift_binary (op : β → β → β') (l r : TTerm α β) : TTerm α β' :=
  bind (fun x => lift_unary (op x) r) l

/-- The evaluation of f for x. -/
@[simp]
def evaluation (x : σ) (f : TTerm α β) : β :=
  match f with
  | Leaf r => r
  | Node p f₁ f₂ =>
    if denote p x then
      evaluation x f₁
    else
      evaluation x f₂

notation f "[" x "]" => evaluation x f

theorem liftU (op : β → β') (f : TTerm α β) (x : σ) :
  (lift_unary op f)[x] = op (f [x]) :=
  match f with
  | Leaf r => rfl
  | Node p ff g => by
    unfold lift_unary evaluation
    match gg : denote p x with
    | true  =>
      simp[fmap,gg]
      rw[←liftU op] -- inductive hypothesis
      unfold lift_unary; simp
    | false =>
      simp[fmap,gg]
      rw[←liftU op]  -- inductive hypothesis
      unfold lift_unary; simp

/-- Evaluation is a homomorphism. -/
theorem liftB (op : β → β → β') (f g : TTerm α β) (x : σ) :
  (lift_binary op f g)[x] = (op (f [x]) (g [x])) :=
  match f, g with
  | Leaf f1, Leaf g1 => rfl
  | Node p ff gg, Leaf g1 => by
    have ih := liftB op ff (Leaf g1) x
    match gg1 : denote p x with
    | true  =>
      simp[TTerm.bind,join,gg1]
      simp at ih; rw[←ih] -- inductive hypothesis
      simp[lift_unary,lift_binary]
    | false =>
      simp[TTerm.bind,join,gg1]
      have ih1 := liftB op gg (Leaf g1) x
      simp at ih1; rw[←ih1] -- inductive hypothesis
      simp[lift_unary,lift_binary]
  | Leaf f1, Node p ff gg => by
    match hm : denote p x with
    | true  =>
      simp[hm,TTerm.bind,join]
      have g := liftU (op f1) ff x
      simp at g; rw[←g]
      simp[lift_unary]
    | false =>
      simp[hm,TTerm.bind,join]
      have g := liftU (op f1) gg x
      simp at g; rw[←g]
      simp[lift_unary]
  | Node p ff gg, Node p1 ff1 gg1 => by
    match hm : denote p x with
    | true  =>
      simp
      match n2 : denote p1 x with
      | true  =>
        have ih := liftB op ff (Node p1 ff1 gg1) x
        simp[fmap,n2,hm]; simp[n2] at ih -- inductive hypothesis
        rw[←ih]
        simp[lift_unary,lift_binary]
      | false =>
        have ih := liftB op ff (Node p1 ff1 gg1) x
        simp[fmap,n2,hm]; simp[n2] at ih
        rw[←ih] -- inductive hypothesis
        simp[lift_unary,lift_binary]
    | false =>
      match n2:denote p1 x with
      | true  =>
        have ih := liftB op gg (Node p1 ff1 gg1) x
        simp[fmap,n2,hm]; simp[n2] at ih
        rw[←ih] -- inductive hypothesis
        simp[lift_unary,lift_binary]
      | false =>
        have ih := liftB op gg (Node p1 ff1 gg1) x
        simp[fmap,n2,hm]; simp[n2] at ih
        rw[←ih] -- inductive hypothesis
        simp[lift_unary,lift_binary]
