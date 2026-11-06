import Mathlib

theorem number_theory_47576 :
    ¬∃ n : ℤ, 7 ∣ n^2 + 1 := by
  rintro ⟨n, hn⟩
  have h1 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
    omega
  rcases h1 with (h | h | h | h | h | h | h) <;> ( 
    norm_num [Int.dvd_iff_emod_eq_zero, pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod] at hn
    ) <;> ( 
      omega
    )
  <;> try { 
    exfalso <;> tauto
  }