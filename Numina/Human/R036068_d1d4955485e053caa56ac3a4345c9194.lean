import Mathlib

/- 22. Given 5 numbers: $a_{1}=-1, a_{2}=0, a_{3}=1, a_{4}=2, a_{5}=3$. The sixth is the product of the first and the second, the seventh is the product of the second and the third, the eighth is the product of the third and the fourth, and so on. What is the last non-zero number in this sequence? -/
theorem algebra_235094 (a : ℕ → ℤ) (ha : a 0 = -1 ∧ a 1 = 0 ∧ a 2 = 1 ∧ a 3 = 2 ∧ a 4 = 3)
    (h : ∀ n, a (n + 5) = a n * a (n + 1)) :
    a 12 = 12 ∧ ∀ n, n ≥ 13 → a n = 0:= by

      --We first need a few terms.
      have a5 : a 5 = 0 := by simp_all [h]
      have a6 : a 6 = 0 := by simp_all [h]
      have a7 : a 7 = 2 := by simp_all [h]
      have a8 : a 8 = 6 := by simp_all [h]
      have a9 : a 9 = 0 := by simp_all [h]
      have a10: a 10= 0 := by simp_all [h]
      have a11: a 11= 0 := by simp_all [h]
      have a12: a 12 =12:= by simp_all [h]
      have a13 : a 13 = 0 := by simp_all [h]
      have a14 : a 14 = 0 := by simp_all [h]
      have a15 : a 15 = 0 := by simp_all [h]
      have a16 : a 16 = 0 := by simp_all [h]
      have a17 : a 17 = 0 := by simp_all [h]
      have a18 : a 18 = 0 := by simp_all [h]

      --Now use the induction assumption to show that a 12 = 12 and a n = 0 for all n >= 13.
      constructor
      assumption

      intro n hn
      have lem : ∀ m : ℕ, a (m+13) = 0 := by 
        have lem' : ∀ x : ℕ, ∀ m:ℕ,  m ≤ x ∧ 13 ≤ m → a m = 0 := by
          intro x
          induction' x with x hx
          simp
          
          intro m hm
          obtain ⟨hmxp, hm13⟩ := hm
          by_cases hmx: m ≤ x
          apply hx; tauto
          have : m = x + 1 := by omega
          rw [this];
          by_cases xl12 : x < 12
          have : x+1 < 13:= by linarith
          linarith 
          by_cases x12: x = 12; rw[x12]; simp; assumption
          by_cases x13: x = 13; rw[x13]; simp; assumption
          by_cases x14: x = 14; rw[x14]; simp; assumption
          by_cases x15: x = 15; rw[x15]; simp; assumption
          by_cases x16: x = 16; rw[x16]; simp; assumption
          by_cases x17: x = 17; rw[x17]; simp; assumption
          have : 18 ≤ x := by simp_all; omega

          have myeq: a (x + 1 - 5 + 5) = a (x + 1 - 5) * a (x + 1 - 5 + 1) := by apply h (x+1-5)
          have : x+1 = x + 1 - 5 + 5 := by omega
          rw [this]; rw [myeq]
          have : a (x + 1 - 5) = 0:= by 
            have : x + 1 - 5 ≤ x := by omega
            have : 13 ≤ x + 1 - 5 := by omega
            apply hx; tauto
          rw [this]; ring_nf



        intro m
        apply lem' (m+13); omega

      have eq : n - 13 + 13 = n := by omega
      have : a (n-13+13) = 0:= by apply lem (n-13)
      rw [eq] at this; assumption
    
