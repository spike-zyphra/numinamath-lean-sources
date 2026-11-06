import Mathlib

/-
There is a six-digit number $\overline{ABCDEF}$, and Xiao Bei found that $\overline{ABC} \times \overline{DEF}$ equals $\frac{1}{7}$ of the six-digit number. Find the value of $\overline{ABCDEF}$.
-/

theorem number_theory_631106 (A B C D E F : ℕ) (hA: 0 < A) (h₀ : A < 10) (h₁ : B < 10) (h₂ : C < 10) (h₃ : D < 10) (h₄ : E < 10) (h₅ : F < 10) (h₆ : (A * 100 + B * 10 + C) * (D * 100 + E * 10 + F) = ((A * 100000 + B * 10000 + C * 1000 + D * 100 + E * 10 + F) : ℚ) / 7) :
A * 100000 + B * 10000 + C * 1000 + D * 100 + E * 10 + F = 143143 := by 

  --Let a = 100A+10B+C and b = 100D+10E +F.
  let a := A * 100 + B * 10 + C
  let b := D * 100 + E * 10 + F

  have al: 100 ≤ a := by omega
  have au: a ≤ 999 := by omega
  have bu: b ≤ 999 := by omega

  have cla : 1000 * a + b = A * 100000 + B * 10000 + C * 1000 + D * 100 + E * 10 + F := by ring_nf

  have eq: a * b = (1000*a + b) / (7:ℚ) := by
    qify at cla
    rw [cla]
    simp [a,b]
    assumption

  have eq2: 7*(a*b) = 1000*a+b := by qify; nlinarith

  have eq3: (7*(a:ℤ)-1)*(7*b-1000) = 1000 := by nlinarith

  have a7p: 0 < (7*(a:ℤ)-1) := by linarith
  have b7p: 0 < (7*(b:ℤ)-1000) := by nlinarith

  --We rewrite our assumption and get the following claim, so 7a-1 ∣ 1000.
  have eq4: (7*a-1)*(7*b-1000) = 1000 := by 
    zify
    have : @Nat.cast ℤ AddMonoidWithOne.toNatCast (7 * a - 1) = @HSub.hSub ℤ ℤ ℤ instHSub (7 * ↑a) 1 := by omega
    rw [this]
    have : @Nat.cast ℤ AddMonoidWithOne.toNatCast (7 * b - 1000)  = @HSub.hSub ℤ ℤ ℤ instHSub (7 * ↑b) 1000 := by omega
    rw [this]
    exact eq3

  --Since 7a-1 ≥ 699, we have 7a-1 = 1000, so a = 143.
  have ae: a = 143 := by 
    have d7a: 7*a-1 ∣ 1000 := by use 7*b-1000; symm; exact eq4
    obtain ⟨k,hk⟩ := d7a
    have ke: k = 1 := by 
      have a7m1699: 699≤ 7*a-1 := by omega
      have knn0 : k ≠ 0:= by 
        by_contra ke0
        rw [ke0] at hk
        norm_num at hk
      by_contra nke1
      have : 2 ≤ k := by omega
      have : 699*2 ≤ (7 * a - 1) * k := by gcongr
      have : 1000 < 699*2 := by omega
      linarith
    rw [ke] at hk
    field_simp at hk
    omega


  --Then b = 143 by simple calculation.
  have be: b = 143 := by rw [ae] at eq2; omega

  rw [← cla]
  linarith