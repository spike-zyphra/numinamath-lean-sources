import Mathlib

open Set BigOperators

theorem my_favorite_theorem : ∑ᶠ x ∈ {x : ℤ | x > 0 ∧ ∃ y : ℤ, y > 0 ∧ x^2 + x + 100 = y^2}, x = 143 := by 
  -- prove the set equal  {x : ℤ | x > 0 ∧ ∃ y : ℤ, y > 0 ∧ x^2 + x + 100 = y^2} =  {99} ∪ {32} ∪ {12}
  have set_eq : {x : ℤ | x > 0 ∧ ∃ y : ℤ, y > 0 ∧ x^2 + x + 100 = y^2} = 
    {99} ∪ {32} ∪ {12} := by 
    simp
    ext x
    constructor
    · intro h
      simp at h
      obtain ⟨hx, y, hy, heq⟩ := h
      -- 4 * x ^ 2 + 4 * x + 400 = 4 * y ^ 2
      have eq_aux1 : 4 * x ^ 2 + 4 * x + 400 = 4 * y ^ 2 := by nlinarith
      have eq_aux2 : (2 * x + 1) ^ 2 + 399 = 4 * y ^ 2 := by nlinarith
      have eq_aux3 : (2 * y + 2 * x + 1) * (2 * y - 2 * x - 1) = 3 * 7 * 19 := by
        nlinarith
      have lt_aux : (2 * y - 2 * x - 1) < (2 * y + 2 * x + 1) := by linarith
      have dvd_aux1 : (2 * y - 2 * x - 1) ∣ 3 * 7 * 19 := by 
        rw [←eq_aux3]; simp
      have le_aux : (2 * y - 2 * x - 1) ≤ 19 := by 
        nlinarith
      have ge_aux : (2 * y - 2 * x - 1) ≥ 1 := by 
        nlinarith
      -- discuss the possibile value of 2 * y - 2 * x - 1
      have eq_or : (2 * y - 2 * x - 1) = 1 ∨ (2 * y - 2 * x - 1) = 3 ∨ 
        (2 * y - 2 * x - 1) = 7 ∨ (2 * y - 2 * x - 1) = 19 := by 
        interval_cases (2 * y - 2 * x - 1)
        left; rfl
        norm_num at dvd_aux1
        right; left; rfl
        norm_num at dvd_aux1
        norm_num at dvd_aux1
        norm_num at dvd_aux1
        right; right; left; rfl
        norm_num at dvd_aux1
        norm_num at dvd_aux1
        norm_num at dvd_aux1
        norm_num at dvd_aux1
        norm_num at dvd_aux1
        norm_num at dvd_aux1
        norm_num at dvd_aux1
        norm_num at dvd_aux1
        norm_num at dvd_aux1
        norm_num at dvd_aux1
        norm_num at dvd_aux1
        right; right; right; rfl
      obtain eq_1 | eq_3 | eq_7 | eq_19 := eq_or
      -- the case 2 * y - 2 * x - 1 = 1
      rw [eq_1] at eq_aux3
      norm_num at eq_aux3
      have xeq : x = 99 := by nlinarith
      simp
      right; right; exact xeq
      -- the case 2 * y - 2 * x - 1 = 3
      rw [eq_3] at eq_aux3
      norm_num at eq_aux3
      have aux : (2 * y + 2 * x + 1) = 133 := by 
        nlinarith
      have xeq : x = 32 := by nlinarith
      simp
      right; left; exact xeq
      -- the case 2 * y - 2 * x - 1 = 7
      rw [eq_7] at eq_aux3
      norm_num at eq_aux3
      have aux : (2 * y + 2 * x + 1) = 57 := by
        nlinarith
      have xeq : x = 12 := by nlinarith
      simp
      left; exact xeq
      -- the case 2 * y - 2 * x - 1 = 19
      rw [eq_19] at eq_aux3
      norm_num at eq_aux3
      have aux : (2 * y + 2 * x + 1) = 21 := by 
        nlinarith
      have xeq : x = 5 := by nlinarith
      have yeq : y = -1 := by nlinarith
      rw [yeq] at hy
      by_contra hc
      linarith
    intro h
    simp at h
    obtain h1 | h2 | h3 := h
    simp
    constructor
    rw [h1]
    norm_num
    use 16
    constructor
    norm_num
    rw [h1]; norm_num
    constructor
    rw [h2]
    norm_num
    use 34
    constructor
    norm_num
    rw [h2]; norm_num
    constructor
    rw [h3]; norm_num
    use 100
    constructor
    norm_num
    rw[h3]; norm_num
  rw [set_eq]
  have fin1 : Set.Finite {(99 : ℤ)} := by simp
  have fin2 : Set.Finite {(32 : ℤ)} := by simp
  have fin3 : Set.Finite {(12 : ℤ)} := by simp
  have disj1 : Disjoint {32} {12} (α := Set ℤ) := by 
    refine disjoint_singleton.mpr ?_
    norm_num
  rw [finsum_mem_union, finsum_mem_union]
  simp
  refine disjoint_singleton.mpr ?_
  norm_num
  exact fin1
  exact fin2
  refine Disjoint.union_left ?_ disj1
  refine disjoint_singleton.mpr ?_
  norm_num
  exact Finite.union fin1 fin2
  exact fin3