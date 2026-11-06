import Mathlib

theorem  algebra_314732 : ((69^5 + 5 * 69^4 + 10 * 69^3 + 10 * 69^2 + 5 * 69 + 1).divisors.card = 216) := by 
  have eq_aux : 69^5 + 5 * 69^4 + 10 * 69^3 + 10 * 69^2 + 5 * 69 + 1 = 
    (69 + 1) ^ 5 := by 
    simp
  have eq_aux2 : 69^5 + 5 * 69^4 + 10 * 69^3 + 10 * 69^2 + 5 * 69 + 1 
    = 2 ^ 5 * 5 ^ 5 * 7 ^ 5 := by 
    rw [eq_aux]
    norm_num
  rw [eq_aux2]
  rw [Nat.card_divisors]
  have set_eq : (2 ^ 5 * 5 ^ 5 * 7 ^ 5).primeFactors
    = {2, 5, 7} := by 
    refine (Finset.erase_eq_iff_eq_insert ?_ ?_).mp ?_
    simp
    constructor
    norm_num
    norm_num
    simp
    refine Eq.symm ((fun {α} {s₁ s₂} => Finset.ext_iff.mpr) ?_)
    intro x
    constructor
    intro h
    simp at h
    obtain hx | hx := h
    refine Finset.mem_erase_of_ne_of_mem ?_ ?_
    rw [hx]
    norm_num
    simp
    constructor
    rw [hx];norm_num
    rw [hx]; norm_num
    refine Finset.mem_erase_of_ne_of_mem ?_ ?_
    rw [hx]
    norm_num
    simp
    constructor
    rw [hx];norm_num
    rw [hx]; norm_num
    intro h
    simp at h
    obtain ⟨h1, h2, h3⟩ := h
    have eq1 : 1680700000 = 2 ^ 5 * (5 ^ 5 * 7 ^ 5) := by norm_num
    rw [eq1] at h3
    have xdvd1 : x ∣ 2 ^ 5  ∨ x ∣  (5 ^ 5 * 7 ^ 5) := by 
      exact (Nat.Prime.dvd_mul h2).mp h3
    obtain hdx | hdx := xdvd1
    have xdvd2 : x ∣ 2 := by 
      exact Nat.Prime.dvd_of_dvd_pow h2 hdx
    have xeq : x ≤ 2 := by 
      exact (Nat.Prime.dvd_factorial h2).mp xdvd2
    interval_cases x 
    norm_num at h2
    norm_num at h2
    simp at h1
    have xdvd4 : x ∣ 5 ^ 5 ∨ x ∣ 7 ^ 5 := by 
      exact (Nat.Prime.dvd_mul h2).mp hdx
    obtain hdx | hdx := xdvd4
    have xdvd5 : x ∣ 5 := by
      exact Nat.Prime.dvd_of_dvd_pow h2 hdx
    have xeq : x ≤ 5 := by
      apply Nat.le_of_dvd
      positivity
      exact xdvd5
    interval_cases x
    all_goals norm_num at h2; 
    norm_num at xdvd5
    norm_num at xdvd5
    simp
    have xdvd5 : x ∣ 7 := by
      exact Nat.Prime.dvd_of_dvd_pow h2 hdx
    have xeq : x ≤ 7 := by
      apply Nat.le_of_dvd
      positivity
      exact xdvd5
    interval_cases x
    all_goals norm_num at h2; 
    norm_num at xdvd5
    norm_num at xdvd5
    simp
    simp
  rw [set_eq]
  simp
  have eq1 : 1680700000 = 2 ^ 5 * (5 ^ 5 * 7 ^ 5) := by norm_num
  rw [eq1]
  have aux1 : (2 ^ 5 * (5 ^ 5 * 7 ^ 5)).factorization 2
    = 5 := by 
    rw [Nat.factorization_def, padicValNat_def']
    refine multiplicity_eq_of_emultiplicity_eq_some ?_
    refine emultiplicity_eq_coe.mpr ?_
    norm_num
    norm_num
    norm_num
    norm_num
  have aux2 : (2 ^ 5 * (5 ^ 5 * 7 ^ 5)).factorization 5
    = 5 := by 
    rw [Nat.factorization_def, padicValNat_def']
    refine multiplicity_eq_of_emultiplicity_eq_some ?_
    refine emultiplicity_eq_coe.mpr ?_
    norm_num
    norm_num
    norm_num
    norm_num
  have aux3 : (2 ^ 5 * (5 ^ 5 * 7 ^ 5)).factorization 7
    = 5 := by 
    rw [Nat.factorization_def, padicValNat_def']
    refine multiplicity_eq_of_emultiplicity_eq_some ?_
    refine emultiplicity_eq_coe.mpr ?_
    norm_num
    norm_num
    norm_num
    norm_num
  rw [aux1, aux2, aux3]
  norm_num
  norm_num