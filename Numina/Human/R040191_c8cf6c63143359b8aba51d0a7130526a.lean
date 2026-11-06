import Mathlib

-- Find the smallest positive integer $n$ such that $107 n$ has the same last two digits as $n$.
theorem number_theory_608283 : (∀ n ∈ {n :ℤ | n > 0 ∧ 107 * n % 100 = n % 100} , 50 ≤ n) ∧ 50 ∈ {n :ℤ | n > 0 ∧ 107 * n % 100 = n % 100} := by
  -- 50 The two numbers have the same last two digits if and only if 100 divides their difference $106 n$, which happens if and only if 50 divides $n$.
  have h : {n :ℤ | n > 0 ∧ 107 * n % 100 = n % 100} = {n :ℤ | n > 0 ∧ 50 ∣ n} := by
    ext n ;simp ;intro hn ;constructor
    · intro h
      have : (107 * n - n) % 100 = 0 := by
        have : (107 * n - n) % 100 = (107 * n % 100 - n % 100) % 100 := by exact Int.sub_emod (107 * n) n 100
        rw [this,h] ;simp
      norm_num at this
      have this' : 107 * n - n = 100 * n + 6 * n := by ring
      rw [this'] at this
      apply (dvd_add_right (by simp)).mp at this
      replace this : 50 * 2 ∣ (3 * n) * 2 := by ring_nf ;rw [mul_comm] ;exact this
      apply (mul_dvd_mul_iff_right (Ne.symm (NeZero.ne' 2))).mp at this
      exact Int.dvd_of_dvd_mul_right_of_gcd_one this rfl
    intro h
    rcases h with ⟨n',h⟩
    by_cases hn' : Even n'
    · rcases hn' with ⟨k,hn'⟩
      rw [hn',← two_mul,← mul_assoc] at h ;norm_num at h
      rw [h] ;simp ;rw [mul_comm,mul_assoc] ;simp
    simp at hn' ;rcases hn' with ⟨k,hn'⟩
    rw [h,hn']
    have : 50 * (2 * k + 1) % 100 = (100 * k + 50) % 100 := by ring_nf
    have this' : 107 * (50 * (2 * k + 1)) % 100 = (100 * (107 * k + 53) + 50) % 100 := by ring_nf
    rw [this,this'] ;refine (Int.emod_add_cancel_right 50).mpr ?_ ;simp
  rw [h]
  constructor
  · intro n hn ;simp at hn
    rcases hn with ⟨hn,hn'⟩
    exact Int.le_of_dvd hn hn'
  simp
  