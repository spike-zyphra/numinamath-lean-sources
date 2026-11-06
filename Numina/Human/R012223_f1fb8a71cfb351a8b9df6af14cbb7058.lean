import Mathlib

/- 10. Let $f(x)=x^{2}-2 x$. How many distinct real numbers $c$ satisfy $f(f(f(f(c))))=3$ ? -/
theorem algebra_15959 {f : ℝ → ℝ} (hf : f = fun x => x ^ 2 - 2 * x) :
    Set.encard {c | f (f (f (f c))) = 3} = 9 := by

  -- Lemma: $f(x) = y$ has two solutions for $y > -1$:
  -- $x = 1 + \sqrt{y + 1}$ and $x = 1 - \sqrt{y + 1}$
  have H₀ {y} (hc : y > -1) : ∀ x, f x = y ↔ x = 1 + √(y + 1) ∨ x = 1 - √(y + 1) := by
    intro c
    rw [hf]
    -- Use the method of completing the square
    rw [show c ^ 2 - 2 * c = y ↔ (c - 1) ^ 2 = y + 1 by constructor <;> intro h <;> linarith]
    -- Trivial simplification
    nth_rw 1 [show y + 1 = (√(y + 1)) ^ 2 by simp [show y + 1 ≥ 0 by linarith]]
    rw [show c = 1 + √(y + 1) ↔ c - 1 = √(y + 1) by constructor <;> intro h <;> linarith]
    rw [show c = 1 - √(y + 1) ↔ c - 1 = -√(y + 1) by constructor <;> intro h <;> linarith]
    exact sq_eq_sq_iff_eq_or_eq_neg

  -- Lemma: $f(x) = y$ has two solutions for $y > -1$
  have H₀' {y} (hc : y > -1) : {x | f x = y}.encard = 2 := by
    rw [Set.ext (H₀ hc), show {c | c = 1 + √(y + 1) ∨ c = 1 - √(y + 1)} = {1 + √(y + 1), 1 - √(y + 1)} by rfl, Set.encard_pair]
    linarith [show √(y + 1) > 0 from Real.sqrt_pos.2 (by linarith)]

  -- f c = 3 ↔ c = 3 ∨ c = -1 by solving the quadratic equation
  have H₁ c : f c = 3 ↔ c = 3 ∨ c = -1 := by
    simp [hf]
    constructor <;> intro h
    . contrapose! h
      nlinarith (config := {splitNe := true})
    . obtain h | h := h
      all_goals
        subst c
        norm_num

  -- f (f (f (f c))) = 3 ↔ c = 3 ∨ c = -1 ∨ f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1
  -- by repeatedly applying the lemma H1
  have H₂ c : f (f (f (f c))) = 3 ↔ c = 3 ∨ c = -1 ∨ f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1 := by
    repeat
      rw [H₁]
    tauto

  -- f c = -1 ↔ c = 1 by solving the quadratic equation
  have H₃ c : f c = -1 ↔ c = 1 := by
    simp [hf]
    constructor <;> intro h
    . contrapose! h
      nlinarith (config := {splitNe := true})
    . subst c
      norm_num

  -- f (f c) = -1 ↔ f c = 1 by the previous lemma
  have H₄ c : f (f c) = -1 ↔ f c = 1 := H₃ _

  -- f (f c) = -1 ↔ c = 1 + √2 ∨ c = 1 - √2 by solving the quadratic equation
  replace H₄ c : f (f c) = -1 ↔ c = 1 + √2 ∨ c = 1 - √2 := by
    rw [H₄, H₀ (by norm_num)]
    norm_num

  -- f (f (f c)) = -1 ↔ f c = 1 + √2 ∨ f c = 1 - √2 by applying the previous lemma
  have H₅ c : f (f (f c)) = -1 ↔ f c = 1 + √2 ∨ f c = 1 - √2 := H₄ _

  -- {c | c = 3} ∩ {c | c = -1 ∨ f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1} = ∅
  have K₁ : Disjoint {c | c = 3} {c | c = -1 ∨ f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1} := by
    simp [Set.disjoint_iff_forall_ne, hf]
    norm_num

  -- {c | f c = -1} ∩ {c | f (f c) = -1 ∨ f (f (f c)) = -1} = ∅
  have K₂ : Disjoint {c | c = -1} {c | f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1} := by
    simp [Set.disjoint_iff_forall_ne, hf]
    norm_num

  -- {c | f c = -1} ∩ {c | f (f c) = -1} = ∅
  have K₃ : Disjoint {c | f c = -1} {c | f (f c) = -1 ∨ f (f (f c)) = -1} := by
    simp [Set.disjoint_iff_forall_ne]
    intro a ha b hb hab
    subst a
    rw [ha, hf] at hb
    norm_num at hb

  -- {c | f (f c) = -1} ∩ {c | f (f (f c)) = -1} = ∅
  have K₄ : Disjoint {c | f (f c) = -1} {c | f (f (f c)) = -1} := by
    simp [Set.disjoint_iff_forall_ne]
    intro a ha b hb hab
    subst a
    rw [ha, hf] at hb
    norm_num at hb

  -- {c | f (f (f c)) = -1} has 4 elements
  have S₁ : {c | f (f (f c)) = -1}.encard = 4 := by
    rw [Set.ext H₅, show {c | f c = 1 + √2 ∨ f c = 1 - √2} = {c | f c = 1 + √2} ∪ {c | f c = 1 - √2} by rfl, Set.encard_union_eq]
    -- 2 elements from the solution of f c = 1 + √2
    -- and 2 elements from the solution of f c = 1 - √2
    . rw [H₀', H₀']
      . norm_num
      . suffices _ : √2 < 2 by linarith
        suffices _ : √2 ^ 2 < 2 ^ 2 by nlinarith
        norm_num
      . linarith [show √2 > 0 by simp]
    -- The two sets are disjoint, trivially
    . simp [Set.disjoint_iff_forall_ne]
      intro a ha b hb hab
      subst a
      rw [hb] at ha
      linarith [show √2 > 0 by simp]

  -- {c | f (f c) = -1} has 2 elements
  have S₂ : {c | f (f c) = -1}.encard = 2 := by
    rw [Set.ext H₄, show {c | c = 1 + √2 ∨ c = 1 - √2} = {1 + √2, 1 - √2} by rfl, Set.encard_pair]
    linarith [show √2 > 0 by simp]

  -- {c | f (f c) = -1 ∨ f (f (f c)) = -1} has 6 elements as it is the disjoint union of the two sets
  have S₃ : {c | f (f c) = -1 ∨ f (f (f c)) = -1}.encard = 6 := by
    rw [show {c | f (f c) = -1 ∨ f (f (f c)) = -1} = {c | f (f c) = -1} ∪ {c | f (f (f c)) = -1} by rfl, Set.encard_union_eq K₄, S₂, S₁]
    norm_num

  -- {c | f c = -1} has 1 element
  have S₄ : {c | f c = -1}.encard = 1 := by
    rw [Set.ext H₃, show {c : ℝ | c = 1} = {1} by rfl, Set.encard_singleton]

  -- {c | f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1} has 7 elements as it is the disjoint union of the two sets
  have S₅ : {c | f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1}.encard = 7 := by
    rw [show {c | f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1} = {c | f c = -1} ∪ {c | f (f c) = -1 ∨ f (f (f c)) = -1} by rfl, Set.encard_union_eq K₃, S₄, S₃]
    norm_num

  -- {c | c = -1} has 1 element
  have S₆ : {c : ℝ | c = -1}.encard = 1 := by
    rw [show {c : ℝ | c = -1} = {-1} by rfl, Set.encard_singleton]

  -- {c | c = -1 ∨ f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1} has 8 elements as it is the disjoint union of the two sets
  have S₇ : {c | c = -1 ∨ f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1}.encard = 8 := by
    rw [show {c | c = -1 ∨ f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1} = {c | c = -1} ∪ {c | f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1} by rfl, Set.encard_union_eq K₂, S₆, S₅]
    norm_num

  -- {c | c = 3} has 1 element
  have S₈ : {c : ℝ | c = 3}.encard = 1 := by
    rw [show {c : ℝ | c = 3} = {3} by rfl, Set.encard_singleton]

  -- {c | c = 3 ∨ c = -1 ∨ f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1} has 9 elements as it is the disjoint union of the two sets
  have S₉ : {c | c = 3 ∨ c = -1 ∨ f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1}.encard = 9 := by
    rw [show {c | c = 3 ∨ c = -1 ∨ f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1} = {c | c = 3} ∪ {c | c = -1 ∨ f c = -1 ∨ f (f c) = -1 ∨ f (f (f c)) = -1} by rfl, Set.encard_union_eq K₁, S₈, S₇]
    norm_num

  -- The final answer
  rw [Set.ext H₂, S₉]
