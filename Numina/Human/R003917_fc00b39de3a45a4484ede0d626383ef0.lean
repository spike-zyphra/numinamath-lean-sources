import Mathlib

/-
66. $a, b, c$ are all prime numbers, and satisfy $a+b+c+a b c=99$, then $\left|\frac{1}{a}-\frac{1}{b}\right|+\left|\frac{1}{b}-\frac{1}{c}\right|+\left|\frac{1}{c}-\frac{1}{a}\right|=$
-/

theorem number_theory_222156 (a b c : ℕ) (ap : a.Prime) (bp : b.Prime) (cp: c.Prime) (h: a + b + c + a*b*c=99):  |(1 / a : ℝ) - (1 / b)| + |(1 / b : ℝ) - 1 / c| + |(1 / c : ℝ) - 1 / a| = 17/19 := by
  
  --Wlog we may assume that a≤ b≤ c.
  wlog aleb : a ≤ b
  have blea : b ≤ a := by omega
  have : |(1 / b : ℝ) - (1 / a)| + |(1 / a : ℝ) - 1 / c| + |(1 / c : ℝ) - 1 / b| = 17/19 := by
    apply this
    exact bp
    exact ap
    exact cp
    linarith
    exact blea
  simp [abs_sub_comm] at this ⊢
  linarith
  wlog blec : b ≤ c
  have cleb : c ≤ b := by omega
  by_cases alec : a ≤ c
  have : |(1 / a : ℝ) - (1 / c)| + |(1 / c : ℝ) - 1 / b| + |(1 / b : ℝ) - 1 / a| = 17/19 := by
    apply this
    exact ap
    exact cp
    exact bp
    nlinarith
    exact alec
    exact cleb
  simp [abs_sub_comm] at this ⊢
  linarith
  have clae : c ≤ a := by omega
  have : |(1 / c : ℝ) - (1 / a)| + |(1 / a : ℝ) - 1 / b| + |(1 / b : ℝ) - 1 / c| = 17/19 := by
    apply this
    exact cp
    exact ap
    exact bp
    nlinarith
    linarith
    linarith
  simp [abs_sub_comm] at this ⊢
  linarith

  --It cannot happen that all of a b c are odd, so a is 2.
  have ae : a = 2 := by 
    by_contra anne2
    have : 2 ≤ a := by exact Nat.Prime.two_le ap
    have : 2 ≤ b := by exact Nat.Prime.two_le bp
    have : 2 ≤ c := by exact Nat.Prime.two_le cp
    have oa: Odd a := by exact Nat.Prime.odd_of_ne_two ap anne2
    have : ¬ b=2:= by omega
    have ob: Odd b := by exact Nat.Prime.odd_of_ne_two bp this
    have : ¬ c=2:=by omega
    have oc: Odd c := by exact Nat.Prime.odd_of_ne_two cp this
    have : Even (a+b+c+a*b*c):= by
      have t1: Odd (a+b+c) := by refine Even.add_odd ?_ oc; exact Odd.add_odd oa ob
      have t2: Odd (a*b*c) := by refine Nat.odd_mul.mpr ?_; constructor; exact Odd.mul oa ob; exact oc
      exact Odd.add_odd t1 t2
    rw [h] at this
    have : Odd 99 := by use 49; norm_num
    have :¬ Even 99 := by exact Nat.not_even_iff.mpr rfl
    contradiction

  --Then rewriting our equation, we still have that h and c cannot be all odd, so b = 2.
  have be : b = 2 := by
    rw [ae] at h
    have eq : b+c+2*b*c = 97 := by linarith
    by_contra bnne2
    have ob: Odd b := by exact Nat.Prime.odd_of_ne_two bp bnne2
    have : ¬c= 2 := by omega
    have oc: Odd c := by exact Nat.Prime.odd_of_ne_two cp this
    have : Even (b+c+2*b*c) := by
      have t1: Even (b+c) := by exact Odd.add_odd ob oc
      have t2: Even (2*b*c) := by use b*c; ring
      exact Even.add t1 t2
    rw [eq] at this
    have : Odd 97 := by use 48; norm_num
    have : ¬Even 97 := by exact Nat.not_even_iff.mpr rfl;
    contradiction
  --Then we have c = 19.
  have ce : c = 19 := by rw [ae,be] at h; simp at h; linarith
  
  --The claim is now a simple calculation.
  rw [ae,be,ce]
  norm_num
  have : |(17:ℝ) / 38| = 17 / 38  := by simp; linarith
  rw [this]
  field_simp
  ring_nf
