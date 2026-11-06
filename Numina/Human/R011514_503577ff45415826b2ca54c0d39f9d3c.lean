import Mathlib

theorem algebra_619696 :
    {p : ℝ | ∃! x, x ^ 2 - p * x + p = 0}.ncard = 2 := by 
  have discrim_eq_zero_of_existsUnique {a b c : ℝ} (ha : a ≠ 0) (h : ∃! x, a * (x * x) + b * x + c = 0) :
        discrim a b c = 0 := by
        simp_rw [quadratic_eq_zero_iff_discrim_eq_sq ha] at h
        generalize discrim a b c = d at h
        obtain ⟨x, rfl, hx⟩ := h
        specialize hx (-(x + b / a))
        field_simp [ha] at hx
        specialize hx (by ring)
        linear_combination -(2 * a * x + b) * hx
  -- discriminant eq_zero iff there exist unique root
  have discrim_eq_zero_iff {a b c : ℝ} (ha : a ≠ 0) :
    discrim a b c = 0 ↔ (∃! x, a * (x * x) + b * x + c = 0) := by
      refine ⟨fun hd => ?_, discrim_eq_zero_of_existsUnique ha⟩
      simp_rw [quadratic_eq_zero_iff_of_discrim_eq_zero ha hd, existsUnique_eq]
  have set_eq : {p : ℝ | ∃! x, x ^ 2 - p * x + p = 0} = {0}∪{4} := by 
    refine Set.ext ?_
    intro p
    constructor
    · intro hp
      simp at hp
      have eq_aux :∃! x, 1 * (x * x) + (-p) * x + p = 0 := by 
        obtain ⟨x, hx, h1⟩ := hp
        simp at h1
        use x
        simp
        constructor
        nlinarith
        intro y hy
        have hy' : y ^ 2 - p * y + p = 0 := by nlinarith
        obtain h2 := h1 y hy'
        exact h2
      obtain h1 := discrim_eq_zero_of_existsUnique (by linarith) eq_aux
      unfold discrim at h1
      have eq_aux2 : p * (p - 4) = 0 := by 
        rw [←h1]
        ring
      obtain hp1 | hp2 := mul_eq_zero.mp eq_aux2
      left; exact hp1
      right; 
      simp_all
      nlinarith
    intro hp
    simp at hp
    obtain hp1 | hp2 := hp
    simp
    -- case p = 4
    have dis_eq : discrim 1 (-p) p = 0 := by 
      unfold discrim
      rw [hp1]
      norm_num
    obtain h1 := (discrim_eq_zero_iff (by linarith)).mp dis_eq
    obtain ⟨x, hx, h2⟩ := h1
    use x
    constructor
    simp
    nlinarith
    intro y hy
    have hy' : 1 * (y * y) + -p * y + p = 0 := by nlinarith
    specialize h2 y hy'
    exact h2
    -- cases p = 0
    have dis_eq : discrim 1 (-p) p = 0 := by 
      unfold discrim
      rw [hp2]
      norm_num
    obtain h1 := (discrim_eq_zero_iff (by linarith)).mp dis_eq
    obtain ⟨x, hx, h2⟩ := h1
    use x
    constructor
    simp
    nlinarith
    intro y hy
    have hy' : 1 * (y * y) + -p * y + p = 0 := by nlinarith
    specialize h2 y hy'
    exact h2
  have aux : {p : ℝ | ∃! x, x ^ 2 - p * x + p = 0}.ncard = ({(0 : ℝ)}∪{(4 : ℝ)} : Set ℝ).ncard := by
    exact congrArg Set.ncard set_eq
     -- This lemma states that ncard operation is applied on both sides of equality.
  rw [aux]
  simp