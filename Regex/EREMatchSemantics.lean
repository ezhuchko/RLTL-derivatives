import Regex.TTerm
import Regex.Metrics

/-!
# Match semantics for ERE

Contains the specification of the matching relation, which follows the same approach
of language-based matching.
The semantics is provided directly as an inductive predicate, in Prop.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ] [DecidableEq α]

open List TTerm ERE

def nullable (r : ERE α) : Bool :=
  match r with
  | ε          => true
  | ERE.Pred _ => false
  | l ⋓ r      => nullable l || nullable r
  | l ⋒ r      => nullable l && nullable r
  | l ⬝ r      => nullable l && nullable r
  | _*         => true
  | ~ r        => !nullable r
  | _ : _      => false

def OneStep' (tr : TTerm α (ERE α)) : α :=
  match tr with
  | Leaf r     => if nullable r then ⊤ else ⊥
  | Node α f g => (α ⊓ OneStep' f) ⊔ (αᶜ ⊓ OneStep' g)

def ERE.derivative (r : ERE α) : TTerm α (ERE α) :=
  match r with
  | ε          => TTerm.pure (Pred ⊥)
  | ERE.Pred b => Node b (TTerm.pure ε) (TTerm.pure (Pred ⊥))
  | l ⋓ r      => lift_binary (· ⋓ ·) (derivative l) (derivative r)
  | l ⋒ r      => lift_binary (· ⋒ ·) (derivative l) (derivative r)
  | l ⬝ r      =>
    if nullable l then
      lift_binary (· ⋓ ·) (lift_binary (· ⬝ ·) (derivative l) (TTerm.pure r))
                          (derivative r)
    else
      lift_binary (· ⬝ ·) (derivative l) (TTerm.pure r)
  | r *   => lift_binary (· ⬝ ·) (derivative r) (TTerm.pure r*)
  | ~ r   => lift_unary (~ ·) (derivative r)
  | l : r =>
    lift_binary (· ⋓ ·) (Node (OneStep' (ERE.derivative l)) (derivative r) (TTerm.pure (Pred ⊥)))
                        (lift_unary (· : r) (derivative l))
prefix:max " δ " => ERE.derivative

/-- The match semantics of ERE are formalised using the models relation. -/
def ERE.models (xs : List σ) (r : ERE α) : Prop :=
  match r with
  | ε          => xs = []
  | ERE.Pred p => ∃ c, xs = [c] ∧ c ⊨ p
  | l ⋓ r      =>
    have : star_metric l < (star_metric (l ⋓ r)) := star_metric_altL
    have : star_metric r < (star_metric (l ⋓ r)) := star_metric_altR
    ERE.models xs l ∨ ERE.models xs r
  | l ⋒ r      =>
    have : star_metric l < (star_metric (l ⋒ r)) := star_metric_interL
    have : star_metric r < (star_metric (l ⋒ r)) := star_metric_interR
    ERE.models xs l ∧ ERE.models xs r
  | l ⬝ r      =>
    ∃ (u₁ u₂ : List σ),
          have : star_metric l < (star_metric (l ⬝ r)) := star_metric_catL
          have : star_metric r < (star_metric (l ⬝ r)) := star_metric_catR
          ERE.models u₁ l
        ∧ ERE.models u₂ r
        ∧ u₁ ++ u₂ = xs
  | r *        =>
    ∃ (m : ℕ),
    have : star_metric (repeat_cat r m) < star_metric r* := star_metric_star
    ERE.models xs (repeat_cat r m)
  | ~ r        =>
    have : star_metric r < (star_metric (~ r)) := star_metric_neg
    ¬ ERE.models xs r
  | l : r      =>
    ∃ (u₁ u₂ : List σ) (c : σ),
          have : star_metric l < (star_metric (l : r)) := star_metric_catL
          have : star_metric r < (star_metric (l : r)) := star_metric_catR
          ERE.models (u₁ ++ [c]) l
        ∧ ERE.models (c::u₂) r
        ∧ u₁ ++ [c] ++ u₂ = xs
termination_by star_metric r
decreasing_by
  repeat (simp_wf; assumption)
notation:52 lhs:53 " ⊫ " rhs:53 => ERE.models lhs rhs

theorem equivalenceNull {r : ERE α} :
  [] ⊫ r ↔ nullable r :=
  match r with
  | ε      => by simp[ERE.models,nullable]
  | Pred p => by simp[ERE.models,nullable]
  | l ⋓ r  => by simp[ERE.models,nullable]; rw[←equivalenceNull,←equivalenceNull]
  | l ⋒ r  => by simp[ERE.models,nullable]; rw[←equivalenceNull,←equivalenceNull]
  | l ⬝ r  => by simp[ERE.models,nullable]; rw[←equivalenceNull,←equivalenceNull]
  | r *    => by simp[ERE.models,nullable]; exists 0
  | ~ r    => by simp only [ERE.models,nullable]; rw[equivalenceNull]; simp
  | l : r  => by simp[ERE.models,nullable]

theorem denoteOneStep' {f : TTerm α (ERE α)} :
  [] ⊫ f [a] ↔ a ⊨ (OneStep' f) := by
  unfold OneStep'
  match f with
  | Leaf rr =>
    simp[equivalenceNull]
    by_cases h : nullable rr
    . simp[h]
    . simp[h]
  | Node g g1 g2 =>
    by_cases h : denote g a
    . simp[h]
      apply Iff.intro
      . intro h1
        erw[denoteOneStep'] at h1 -- inductive hypothesis
        simp at h1; exact h1
      . intro h1
        erw[←denoteOneStep'] at h1 -- inductive hypothesis
        exact h1
    . simp[h]
      apply Iff.intro
      . intro h1
        erw[denoteOneStep'] at h1 -- inductive hypothesis
        simp at h1; exact h1
      . intro h1
        erw[←denoteOneStep'] at h1 -- inductive hypothesis
        exact h1

theorem denoteOneStep {r : ERE α} :
  [] ⊫ (δ r) [a] ↔ (a ⊨ OneStep' (derivative r)) := by
  match g : ERE.derivative r with
  | Leaf f =>
    simp[g,OneStep',equivalenceNull]; aesop
  | Node p f g =>
    simp[g,OneStep']
    match denote p a with
    | true =>
      apply Iff.intro
      . intro h; simp at h; simp; apply denoteOneStep'.mp h
      . intro h
        match h with
        | Or.inl h1 =>
          simp at h1; simp
          apply denoteOneStep'.mpr h1
        | Or.inr h1 =>
          simp at h1 -- contradiction
    | false =>
      apply Iff.intro
      . intro h; simp; simp at h; apply denoteOneStep'.mp h
      . intro h
        match h with
        | Or.inl h1 =>
          simp at h1 -- contradiction
        | Or.inr h1 =>
          simp; simp at h1
          apply denoteOneStep'.mpr h1

theorem derives_Star {r : ERE α} (h : a :: xs ⊫ r⁽n⁾) :
  ∃ u₁, a::u₁ ⊫ r ∧ ∃ x, (∃ m, x ⊫ r⁽m⁾) ∧ u₁ ++ x = xs := by
  match n with
  | 0 => simp[ERE.models] at h
  | .succ n =>
    simp[ERE.models] at h
    let ⟨u1,h1,u2,h2,h3⟩ := h
    match u1 with
    | [] =>
      simp at h3; subst h3
      have ih := derives_Star h2
      simp_all only
    | .cons z zs =>
      match xs with
      | [] =>
        simp at h3; let ⟨k1,k2,k3⟩ := h3
        subst k1 k2 k3; simp; exact ⟨h1,⟨n,h2⟩⟩
      | .cons x xs =>
        simp at h3; let ⟨k1,k2⟩ := h3; subst k1
        exact ⟨zs,h1,⟨u2,⟨n,h2⟩,k2⟩⟩

theorem equivalenceDer {r : ERE α} :
  a::xs ⊫ r ↔ xs ⊫ (δ r)[a] :=
  match r with
  | ε => by simp[ERE.models,evaluation,ERE.derivative]
  | ERE.Pred p => by
    simp[ERE.models,evaluation,ERE.derivative]
    by_cases h : denote p a
    . simp[h,ERE.models]
      apply Iff.intro
      . intro ⟨_,⟨_,x2⟩,_⟩; subst x2; rfl
      . intro h1; subst h1; exact ⟨a,⟨⟨rfl,rfl⟩,h⟩⟩
    . simp[h,ERE.models]
  | l ⋓ r => by
    simp only [ERE.models,evaluation,ERE.derivative]
    rw[equivalenceDer,equivalenceDer,liftB] -- inductive hypothesis
    simp[ERE.models]
  | l ⋒ r => by
    simp only [ERE.models,evaluation,ERE.derivative]
    rw[equivalenceDer,equivalenceDer,liftB] -- inductive hypothesis
    simp[ERE.models]
  | r * => by
    simp only [ERE.models,evaluation,ERE.derivative,liftB]
    simp[ERE.models]
    apply Iff.intro
    . intro ⟨n,g⟩
      let ⟨u1,h1,⟨h2,h3,h4⟩⟩ := derives_Star g
      rw[equivalenceDer] at h1 -- inductive hypothesis
      exact ⟨u1,h1,⟨h2,⟨h3,h4⟩⟩⟩
    . intro ⟨h1,h2,h3,⟨n,h4⟩,h5⟩; exists n.succ; simp
      simp[ERE.models]
      match n with
      | 0 =>
        simp [ERE.models] at h4; subst h4; simp at h5; simp; subst h5
        simp[ERE.models]
        rw[equivalenceDer] -- inductive hypothesis
        exact h2
      | .succ n =>
        simp at h4; simp
        match h1 with
        | [] =>
          simp at h5; subst h5
          rw[←equivalenceDer] at h2 -- inductive hypothesis
          exists [a]; exists h2; exists h3
        | .cons rr rs =>
          simp at h5; subst h5
          exists (a::rr::rs)
          rw[←equivalenceDer] at h2 -- inductive hypothesis
          exists h2; exists h3
  | ~ r => by
    simp [ERE.models,evaluation,ERE.derivative,liftU]
    rw[equivalenceDer] -- inductive hypothesis
  | l ⬝ r => by
    simp[ERE.models,evaluation,ERE.derivative]
    by_cases g : nullable l
    . simp[g,liftB,ERE.models]
      apply Iff.intro
      . intro ⟨u,hu,⟨x,hv,hv1⟩⟩
        match u with
        | [] =>
          subst hv1
          apply Or.inr (equivalenceDer.mp hv) -- inductive hypothesis
        | .cons rr rs =>
          simp at hv1; let ⟨k1,k2⟩ := hv1; subst k1
          apply Or.inl ⟨rs,equivalenceDer.mp hu,⟨x,hv,k2⟩⟩ -- inductive hypothesis
      . intro h1
        match h1 with
        | Or.inl ⟨u,hu,⟨x,hv,hv1⟩⟩ =>
          subst hv1; exact ⟨a::u,equivalenceDer.mpr hu,⟨x,hv,rfl⟩⟩ -- inductive hypothesis
        | Or.inr h3 =>
          exact ⟨[],equivalenceNull.mpr g,⟨a::xs,equivalenceDer.mpr h3,rfl⟩⟩ -- inductive hypothesis
    . simp[g,liftB,ERE.models]
      apply Iff.intro
      . intro ⟨h1,h2,⟨h3,h4,h5⟩⟩
        match h1 with
        | [] => simp at h5; subst h5; simp[←equivalenceNull] at g; contradiction
        | .cons rr rs =>
          simp at h5; let ⟨k1,k2⟩ := h5; subst k1
          exact ⟨rs,equivalenceDer.mp h2,⟨h3,h4,k2⟩⟩ -- inductive hypothesis
      . intro ⟨h1,h2,⟨h3,h4,h5⟩⟩
        exact ⟨a::h1,equivalenceDer.mpr h2,⟨h3,h4,by simp; exact h5⟩⟩ -- inductive hypothesis
  | l : r => by
    by_cases g : denote (OneStep' δ l) a = true
    . apply Iff.intro
      . intro h
        simp[models] at h
        let ⟨u1,u2,d,h1,h2,h3⟩ := h; clear h
        match u1 with
        | [] =>
          simp at h1 h2 h3; let ⟨k1,k2⟩ := h3; subst k1 k2; clear h3
          simp only [derivative,liftB,TTerm.pure,liftU]
          simp[g,models]
          apply Or.inl (equivalenceDer.mp h2) -- inductive hypothesis
        | a::as =>
          simp at h1 h2 h3; let ⟨k1,_⟩ := h3; subst k1
          simp only [derivative, liftB, TTerm.pure,liftU]
          simp[g, models]
          apply Or.inr ⟨as,u2,d,(equivalenceDer.mp h1),h2,h3.2⟩ -- inductive hypothesis
      . intro h
        simp only [models,g,derivative,liftB,TTerm.pure,liftU] at h
        simp[g,models] at h
        match h with
        | Or.inl h1 =>
          unfold models; exists []; exists xs; exists a; simp
          have := denoteOneStep.mpr g
          rw[←equivalenceDer] at h1 this -- inductive hypothesis
          exact ⟨this,h1⟩
        | Or.inr ⟨u1,u2,d,h1,h2,h3⟩ =>
          unfold models; exists (a::u1); exists u2; exists d; simp
          rw[←equivalenceDer] at h1 -- inductive hypothesis
          exact ⟨h1,h2,h3⟩
    . apply Iff.intro
      . intro h
        simp[models] at h
        let ⟨u1,u2,d,h1,h2,h3⟩ := h; clear h
        match u1 with
        | [] =>
          simp only [derivative,liftB,TTerm.pure,liftU,g,models]
          simp at h1 h3; let ⟨k1,k2⟩ := h3; subst k1
          rw[equivalenceDer] at h1 -- inductive hypothesis
          have := denoteOneStep (r:=l) (a:=d); unfold modelsEBA at this
          rw[this.mp h1] at g
          contradiction
        | a::as =>
          simp only [derivative,liftB,TTerm.pure,liftU,g,models]
          simp at h1 h3; let ⟨k1,k2⟩ := h3; subst k1; simp
          rw[equivalenceDer] at h1 -- inductive hypothesis
          apply Or.inr ⟨as,u2,d,h1,h2,h3.2⟩
      . intro h
        simp only [derivative,liftB,TTerm.pure,liftU] at h
        simp[g,models] at h
        let ⟨u1,u2,d,h1,h2,h3⟩ := h; clear h
        match u1 with
        | [] =>
          simp at h1 h2 h3; subst h3
          simp only [models]
          rw[←equivalenceDer] at h1 -- inductive hypothesis
          exact ⟨[a],u2,d,h1,h2,rfl⟩
        | b::bs =>
          simp at h1 h2 h3; subst h3
          simp only [models]
          rw[←equivalenceDer] at h1 -- inductive hypothesis
          exact ⟨a::b::bs,u2,d,h1,h2,by simp⟩
