import Mathlib
open Polynomial

/-
92.2. Let $n>1$ be an integer and let $a_{1}, a_{2}, \ldots, a_{n}$ be $n$ different integers. Show that the polynomial


$$

f(x)=\left(x-a_{1}\right)\left(x-a_{2}\right) \cdots\left(x-a_{n}\right)-1

$$


is not divisible by any polynomial with integer coefficients and of degree greater than zero but less than $n$ and such that the highest power of $x$ has coefficient 1.
 -/
theorem algebra_110074 {n : ℕ} (hn : 1 < n) (a : Fin n → ℤ) (ha : Function.Injective a) :
  ¬∃ p : Polynomial ℤ, p.natDegree > 0 ∧ p.natDegree < n ∧ Monic p ∧ p ∣ (∏ i : Fin n, (X - C (a i)) - 1) := by
  -- by contradiction
  intro h
  set f := ∏ i : Fin n, (X - C (a i)) - 1 with hf
  have hf' : f = ∏ i : Fin n, (X +- C (a i)) + C (-1) := by rw [hf, C_neg]; rfl
  have f_deg : f.natDegree = n
  · rw [hf', natDegree_add_C, natDegree_prod (Finset.univ : Finset (Fin n)) (fun i ↦ X +- C (a i))]
    conv_lhs => arg 2; intro i; arg 1; rw [←C_neg]
    conv_lhs => arg 2; intro i; rw [natDegree_add_C, natDegree_X];
    simp
    intro i hi hyp
    apply congr_arg (fun t ↦ coeff t 1) at hyp
    simp at hyp
    have := calc
      0 = 1 - (C (a i)).coeff 1 := hyp.symm
      _ = 1 := by rw [coeff_C_succ, sub_zero]
    contradiction
  rcases h with ⟨p, p_pos, p_deg, p_monic, ⟨g, hg⟩⟩
  have f_z : p * g ≠ 0 := by apply ne_zero_of_natDegree_gt; rw [←hg, f_deg]; exact hn
  have g_z : g ≠ 0 := by exact right_ne_zero_of_mul f_z
  have deg_sum : n = p.natDegree + g.natDegree := by rw [←f_deg, hg]; exact natDegree_mul (ne_zero_of_natDegree_gt p_pos) g_z
  have g_deg : g.natDegree < n := by linarith

  -- evaluate f = p * g at each (a i)
  have h_prod : ∀ i, p.eval (a i) * g.eval (a i) = -1
  · intro i
    rw [←eval_mul, ←hg, hf, eval_sub, eval_prod]
    simp
    rw [Finset.prod_eq_zero_iff]
    exact ⟨i, Finset.mem_univ i, Int.sub_self (a i)⟩
  have h_add : ∀ i, (p + g).eval (a i) = 0
  · intro i
    rw [eval_add]
    cases Int.mul_eq_one_iff_eq_one_or_neg_one.mp (show -p.eval (a i) * g.eval (a i) = 1 by linarith [h_prod i]) <;> linarith
  if h_zero : p + g = 0 then
    -- then f = -p^2, but f and p are monic, contradiction
    have monic_f : Monic f
    · rw [hf]
      apply Monic.sub_of_left
      swap
      · have f_pos : f.degree > 0
        · have n_pos : n > 0 := by linarith
          rw [←degree_eq_iff_natDegree_eq_of_pos n_pos] at f_deg
          rw [f_deg]
          exact_mod_cast n_pos
        rw [show ∏ i, (X - C (a i)) = f + C 1 by rw [hf]; simp, degree_add_C f_pos]
        simp
        exact f_pos
      apply monic_prod_of_monic (Finset.univ : Finset (Fin n)) (fun i ↦ X - C (a i))
      intro i hi
      if a_zero : a i = 0 then rw [a_zero]; simp else
      apply Monic.sub_of_left monic_X
      rw [degree_X, degree_C a_zero]
      exact zero_lt_one' _
    have hfp : f = -p * p := by calc
      f = p * g := hg
      _ = p * (p + g) - p * p := by ring
      _ = -p * p := by rw [h_zero]; ring
    have coeff_pos : leadingCoeff (-p * p) = 1 := by rw [←hfp]; exact monic_f
    have coeff_neg : leadingCoeff (-p * p) = -1 := by rw [leadingCoeff_mul, p_monic, leadingCoeff_neg, p_monic, mul_one]
    rw [coeff_pos] at coeff_neg
    contradiction
  else
  -- the polynomial p + g has at least n roots
  -- but (p + g).degree < n, contradiction
  have hroot : List.ofFn a ≤ (p + g).roots
  · rw [Multiset.le_iff_subset (by exact List.nodup_ofFn_ofInjective ha)]
    intro x hx
    simp only [Multiset.mem_coe, List.mem_ofFn, mem_roots', ne_eq, IsRoot.def, eval_add] at hx ⊢
    rcases hx with ⟨i, hi⟩
    rw [←hi, ←eval_add, h_add i]
    exact ⟨h_zero, rfl⟩
  have : n < n := calc
    n ≤ (p + g).roots.card := by convert Multiset.card_le_card hroot; simp
    _ ≤ (p + g).natDegree := card_roots' (p + g)
    _ ≤ max p.natDegree g.natDegree := natDegree_add_le p g
    _ < n := max_lt p_deg g_deg
  linarith