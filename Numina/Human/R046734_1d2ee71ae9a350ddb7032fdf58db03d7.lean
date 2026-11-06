import Mathlib

open Real

theorem algebra_317397 (t : ℝ → ℝ) (ht : t = fun x => (1/2)^x + (2/3)^x + (5/6)^x) :
    ∑ᶠ x ∈ {x | (t x - 1)*(t x - 2)*(t x - 3) = 0}, x = 4 := by 
  -- t is a strict monitonically decreasing function
  have tmo : StrictAnti t := by 
    have mo1 : StrictAnti (fun (x : ℝ) => (1/(2 : ℝ))^x) := by 
      unfold StrictAnti
      intro x y h
      simp
      calc 
        _ = (2 : ℝ)⁻¹ ^ x * (2⁻¹ ^ (y - x)) := by 
          rw [←rpow_add]
          simp
          linarith
        _ < 2⁻¹ ^ x * 1 := by 
          apply mul_lt_mul_of_pos_left
          refine rpow_lt_one ?_ ?_ ?_
          positivity
          linarith
          linarith
          positivity
        _ = 2⁻¹ ^ x := by 
          simp
    have mo2 : StrictAnti (fun (x : ℝ) => (2/(3 : ℝ))^x) := by 
      unfold StrictAnti
      intro x y h
      simp
      calc 
        _ = (2 / (3 : ℝ)) ^ x * ((2 / (3 : ℝ)) ^ (y - x)) := by 
          rw [←rpow_add]
          simp
          linarith
        _ < (2 / (3 : ℝ)) ^ x * 1 := by 
          apply mul_lt_mul_of_pos_left
          refine rpow_lt_one ?_ ?_ ?_
          positivity
          linarith
          linarith
          positivity
        _ = (2 / (3 : ℝ)) ^ x := by 
          simp
      
    have mo3 : StrictAnti (fun (x : ℝ) => (5/(6 : ℝ))^x) := by 
      unfold StrictAnti
      intro x y h
      simp
      calc 
        _ = (5 / (6 : ℝ)) ^ x * ((5 / (6 : ℝ))  ^ (y - x)) := by 
          rw [←rpow_add]
          simp
          linarith
        _ < (5 / (6 : ℝ))  ^ x * 1 := by 
          apply mul_lt_mul_of_pos_left
          refine rpow_lt_one ?_ ?_ ?_
          positivity
          linarith
          linarith
          positivity
        _ = (5 / (6 : ℝ))  ^ x := by 
          simp
    obtain mo4 := StrictAnti.add mo1 mo2
    obtain mo5 := StrictAnti.add mo4 mo3
    rw [ht]
    exact mo5
  have teq1 : t 0 = 3 := by norm_num [ht]
  have teq2 : t 1 = 2 := by norm_num [ht]
  have teq3 : t 3 = 1 := by norm_num [ht]
  have aux1 : {x | t x - 1 = 0} = {3} := by 
    ext x
    constructor
    intro h
    simp
    simp at h
    unfold StrictAnti at tmo
    by_cases hx : x > 3 
    · by_contra hc
      obtain h1 := tmo hx
      rw [teq3] at h1
      linarith
    by_cases hx' : x < 3
    · by_contra hc
      obtain h1 := tmo hx'
      rw [teq3] at h1
      linarith
    linarith
    intro h
    simp at h
    simp
    rw [h]
    linarith
  have aux2 : {x | t x - 2 = 0} = {1} := by 
    ext x
    constructor
    intro h
    simp
    simp at h
    unfold StrictAnti at tmo
    by_cases hx : x > 1
    · by_contra hc
      obtain h1 := tmo hx
      rw [teq2] at h1
      linarith
    by_cases hx' : x < 1
    · by_contra hc
      obtain h1 := tmo hx'
      rw [teq2] at h1
      linarith
    linarith
    intro h
    simp at h
    simp
    rw [h]
    linarith
  have aux3 : {x | t x - 3 = 0} = {0} := by 
    ext x
    constructor
    intro h
    simp
    simp at h
    unfold StrictAnti at tmo
    by_cases hx : x > 0
    · by_contra hc
      obtain h1 := tmo hx
      rw [teq1] at h1
      linarith
    by_cases hx' : x < 0
    · by_contra hc
      obtain h1 := tmo hx'
      rw [teq1] at h1
      linarith
    linarith
    intro h
    simp at h
    simp
    rw [h]
    linarith
  have fin1 : {x | t x - 1 = 0}.Finite := by
    rw [aux1]; exact Set.finite_singleton 3
  have fin2 : {x | t x - 2 = 0}.Finite := by
    rw [aux2]; exact Set.finite_singleton 1
  have fin3 : {x | t x - 3 = 0}.Finite := by 
    rw [aux3]; exact Set.finite_singleton 0
    
  have fin4 : ({x | t x - 1 = 0} ∪ {x | t x - 2 = 0}).Finite := by 
    exact Set.Finite.union fin1 fin2
  have disj1 : Disjoint ({x | t x - 1 = 0} ∪ {x | t x - 2 = 0}) {x | t x - 3 = 0} := by   
    rw [aux1, aux2, aux3]
    simp
  have disj2 : Disjoint {x | t x - 1 = 0}  {x | t x - 2 = 0} := by 
    rw [aux1, aux2]
    simp
  have set_eq : {x | (t x - 1)*(t x - 2)*(t x - 3) = 0} = 
    {x | t x - 1 = 0} ∪ {x | t x - 2 = 0} ∪  {x | t x - 3 = 0} := by 
    refine Set.ext ?_
    intro x
    constructor
    intro h
    simp at h
    simpa
    intro h
    simpa
  rw [set_eq, finsum_mem_union disj1 fin4 fin3, finsum_mem_union disj2 fin1 fin2]
  -- to prove the equality 
  have eq_aux1 : ∑ᶠ (i : ℝ) (_ : i ∈ {x | t x - 1 = 0}), i = 3 := by 
    rw [finsum_eq_single _ 3]
    simp
    rw [teq3]
    simp
    intro x hx
    have neq : x ∉ {x | t x - 1 = 0} := by 
      by_contra h'
      simp at h'
      by_cases hge : x > 3 
      unfold StrictAnti at tmo
      obtain hc := tmo hge
      rw [teq3] at hc
      linarith
      simp at hge
      obtain h2 := lt_of_le_of_ne hge hx
      unfold StrictAnti at tmo
      obtain hc := tmo h2
      rw [teq3] at hc
      linarith
    simp [neq]
  have eq_aux2 : ∑ᶠ (i : ℝ) (_ : i ∈ {x | t x - 2 = 0}), i = 1 := by 
    rw [finsum_eq_single _ 1]
    simp
    rw [teq2]
    simp
    intro x hx
    have neq : x ∉ {x | t x - 2 = 0} := by 
      by_contra h'
      simp at h'
      by_cases hge : x > 1 
      unfold StrictAnti at tmo
      obtain hc := tmo hge
      rw [teq2] at hc
      linarith
      simp at hge
      obtain h2 := lt_of_le_of_ne hge hx
      unfold StrictAnti at tmo
      obtain hc := tmo h2
      rw [teq2] at hc
      linarith
    simp [neq]
  have eq_aux3 : ∑ᶠ (i : ℝ) (_ : i ∈ {x | t x - 3 = 0}), i = 0 := by 
    rw [finsum_eq_single _ 0]
    simp
    intro x hx
    have neq : x ∉ {x | t x - 3 = 0} := by 
      by_contra h'
      simp at h'
      by_cases hge : x > 0
      unfold StrictAnti at tmo
      obtain hc := tmo hge
      rw [teq1] at hc
      linarith
      simp at hge
      obtain h2 := lt_of_le_of_ne hge hx
      unfold StrictAnti at tmo
      obtain hc := tmo h2
      rw [teq1] at hc
      linarith
    simp [neq]
  rw [eq_aux1, eq_aux2, eq_aux3]
  norm_num