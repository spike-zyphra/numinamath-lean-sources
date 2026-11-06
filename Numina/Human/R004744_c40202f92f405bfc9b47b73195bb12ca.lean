import Mathlib

set_option maxRecDepth 3000

def a (n : ℕ) := ∑ i in Finset.Icc 1 n, i

def S (m : ℕ) := ∑ i in Finset.Icc 1 m, a i

/- # Problem:
 $$
\begin{array}{l}
\text { 6. Let } a_{n}=1+2+\cdots+n\left(n \in \mathbf{Z}_{+}\right) , \\
S_{m}=a_{1}+a_{2}+\cdots+a_{m}(m=1,2, \cdots) \text {. }
\end{array}
$$

Then among $S_{1}, S_{2}, \cdots, S_{2017}$, the numbers that are divisible by 2 but not by 4 are $\qquad$ in number.
$$
6. 252 .
-/
theorem number_theory_315010 :
    Set.ncard {x | ∃ m, x = S m ∧ 2 ∣ x ∧ ¬4 ∣ x ∧ 1 ≤ m ∧ m ≤ 2017} = 252 := by

   -- Notice that, $S_{m}=\frac{m(m+1)(m+2)}{6}$.
  have h_sm: ∀ m, (S m) = m * (m + 1) * (m + 2) / 6 := by
    intro m
    suffices (S m) * 6 = m * (m + 1) * (m + 2) by
      refine Nat.eq_div_of_mul_eq_left ?_ this
      norm_num
    induction m with
    | zero => simp [a, S]
    | succ k ih =>
      simp [S]
      have : ∑ i ∈ Finset.Icc 1 (k + 1), a i = ∑ i ∈ Finset.Icc 1 k, a i + a (k + 1) := by
        apply Finset.sum_Icc_succ_top
        omega
      rw [this]
      simp [S] at ih
      rw [add_mul, ih]
      have ha (k : ℕ) : (a k) * 2 = k * (k + 1) := by
        induction k with
        | zero =>
          simp [a]
        | succ k ih =>
          simp [a, Finset.sum_Icc_succ_top] at ih ⊢
          ring_nf at ih ⊢
          omega
      have : 6 = 2 * 3 := by norm_num
      rw [this]
      clear this
      rw [← mul_assoc]
      simp [ha (k+1)]
      ring

  -- Thus $S_{m} \equiv 2(\bmod 4)$ $$ \begin{array}{l} \Leftrightarrow m(m+1)(m+2) \equiv 4(\bmod 8)$$
  have iff1 (m : ℕ) : S m ≡ 2 [MOD 4] ↔ m * (m + 1) * (m + 2) ≡ 4 [MOD 8] := by
    have h1 : m * (m + 1) * (m + 2) % 6 = 0 := by
      have h2 : m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 := by
        omega
      rcases h2 with (h | h | h | h | h | h) <;> simp [h, Nat.mul_mod, Nat.add_mod]
    constructor
    · -- Forward: if $m * (m + 1) * (m + 2) / 6 ≡ 2 [MOD 4]$ then $m * (m + 1) * (m + 2) ≡ 4 [MOD 8]$
      intro h
      have h4 : (m * (m + 1) * (m + 2)) / 6 % 4 = 2 := by
        simp [Nat.ModEq, h_sm] at h ⊢
        omega
      have h5 : (m * (m + 1) * (m + 2)) % 8 = 4 := by
        have h4' : (m * (m + 1) * (m + 2)) / 6 % 4 = 2 := h4
        omega
      simp [Nat.ModEq]
      omega
    · -- Backward: if $m * (m + 1) * (m + 2) ≡ 4 [MOD 8]$ then $m * (m + 1) * (m + 2) / 6 ≡ 2 [MOD 4]$
      intro h
      have h2 : (m * (m + 1) * (m + 2)) % 8 = 4 := by
        simp [Nat.ModEq] at h ⊢
        omega
      have h4 : (m * (m + 1) * (m + 2) / 6) % 4 = 2 := by
        omega
      simp [Nat.ModEq, h_sm]
      omega

  -- $$\Leftrightarrow m \equiv 3(\bmod 8) . \end{array} $$
  have iff2 (m : ℕ) : m * (m + 1) * (m + 2) ≡ 4 [MOD 8] ↔ m ≡ 3 [MOD 8] := by
    have h1 : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by
      omega
    rcases h1 with (h | h | h | h | h | h | h | h) <;>
      simp [Nat.ModEq, h, Nat.mul_mod, Nat.add_mod, Nat.mul_mod, Nat.add_mod]

  -- Therefore, among $S_{1}, S_{2}, \cdots, S_{2017}$, the numbers that are divisible by 2 but not by 4 are $\left[\frac{2017}{8}\right]=252$ in total. -/
  have claim1 :  Set.ncard {x | ∃ m, x = S m ∧ 2 ∣ x ∧ ¬4 ∣ x ∧ 1 ≤ m ∧ m ≤ 2017}
               = Set.ncard {m | m ≡ 3 [MOD 8] ∧ m ≤ 2017} := by
    have h1 :   {x | ∃ m, x = S m ∧ 2 ∣ x ∧ ¬4 ∣ x ∧ 1 ≤ m ∧ m ≤ 2017}
              = {x | ∃ m, x = S m ∧ m ≡ 3 [MOD 8] ∧ 1 ≤ m ∧ m ≤ 2017} := by
      apply Set.ext
      simp
      intro x
      constructor
      . intro H
        obtain ⟨ m, ⟨ hm1, hm2, hm3, hm4⟩ ⟩ := H
        use m
        constructor
        . exact hm1
        . constructor
          . rw[hm1] at hm2 hm3
            apply (iff2 m).mp
            apply (iff1 m).mp
            have h2 : S m % 4 = 2 := by omega
            exact h2
          . exact hm4
      . intro H
        obtain ⟨ m, ⟨ hm1, hm2, hm3, hm4⟩ ⟩ := H
        use m
        constructor
        . exact hm1
        . rw [hm1]
          have : S m ≡ 2 [MOD 4] := by
            apply (iff1 m).mpr
            apply (iff2 m).mpr
            exact hm2
          constructor
          . have h1 : S m % 4 = 2 := by exact this
            have h2 : S m % 2 = 0 := by omega
            exact Nat.dvd_of_mod_eq_zero h2
          . constructor
            . intro h4
              have h1 : S m % 4 = 2 := by exact this
              have h2 : S m % 4 = 0 := by omega
              omega
            . omega

    rw [h1]
    set D := {m | m ≡ 3 [MOD 8] ∧ m ≤ 2017}
    set R := {x | ∃ m : ℕ, x = S m ∧ m ≡ 3 [MOD 8] ∧ 1 ≤ m ∧ m ≤ 2017}

    let f := fun (m : ℕ) (h : m ∈ D) ↦ (S m)
    symm
    apply Set.ncard_congr f
    . intro m hm
      simp [f, R]
      use m
      simp
      simp [D] at hm
      constructor
      . exact hm.1
      . constructor
        . by_contra H
          simp at H
          simp [H] at hm
          revert hm
          decide
        . exact hm.2
    . intro x y
      simp [f, D]
      intro hx hxub hy hyub hSxSy
      simp [h_sm x, h_sm y] at hSxSy
      have h1 : x * (x + 1) * (x + 2) % 6 = 0 := by
        have h2 : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by
          omega
        rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2)
        all_goals simp [h2, Nat.mul_mod, Nat.add_mod]
      have h2 : y * (y + 1) * (y + 2) % 6 = 0 := by
        have h3 : y % 6 = 0 ∨ y % 6 = 1 ∨ y % 6 = 2 ∨ y % 6 = 3 ∨ y % 6 = 4 ∨ y % 6 = 5 := by
          omega
        rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3)
        all_goals simp [h3, Nat.mul_mod, Nat.add_mod]
      have h3 : x * (x + 1) * (x + 2) = y * (y + 1) * (y + 2) := by
        omega
      have h4 : x ≤ y := by
        by_contra h5
        push_neg at h5
        have h6 : x > y := by omega
        have h7 : x ≥ y + 1 := by omega
        have h8 : x * (x + 1) * (x + 2) > y * (y + 1) * (y + 2) := by
          have h9 : x ≥ y + 1 := by linarith
          have h10 : (x : ℕ) ≥ (y + 1 : ℕ) := by linarith
          have h11 : (x + 1 : ℕ) ≥ (y + 2 : ℕ) := by linarith
          have h12 : (x + 2 : ℕ) ≥ (y + 3 : ℕ) := by linarith
          have h13 : (x : ℕ) * (x + 1) * (x + 2) ≥ (y + 1) * (y + 2) * (y + 3) := by
            apply Nat.mul_le_mul
            apply Nat.mul_le_mul
            all_goals linarith
          have h14 : (y + 1) * (y + 2) * (y + 3) > y * (y + 1) * (y + 2) := by
            nlinarith
          exact Nat.lt_of_lt_of_le h14 h13
        linarith
      have h5 : y ≤ x := by
        by_contra h6
        push_neg at h6
        have h7 : y > x := by omega
        have h8 : y ≥ x + 1 := by omega
        have h9 : y * (y + 1) * (y + 2) > x * (x + 1) * (x + 2) := by
          have h10 : y ≥ x + 1 := by linarith
          have h11 : (y : ℕ) ≥ (x + 1 : ℕ) := by linarith
          have h12 : (y + 1 : ℕ) ≥ (x + 2 : ℕ) := by linarith
          have h13 : (y + 2 : ℕ) ≥ (x + 3 : ℕ) := by linarith
          have h14 : (y : ℕ) * (y + 1) * (y + 2) ≥ (x + 1) * (x + 2) * (x + 3) := by
            apply Nat.mul_le_mul
            apply Nat.mul_le_mul
            all_goals linarith
          have h15 : (x + 1) * (x + 2) * (x + 3) > x * (x + 1) * (x + 2) := by
            nlinarith
          exact Nat.lt_of_lt_of_le h15 h14
        linarith
      linarith
    . intro x hx
      simp [R] at hx
      obtain ⟨ m, hm ⟩ := hx
      use m
      simp [D]
      obtain ⟨ h1, h2, h3 ⟩ := hm
      use ⟨ h2, h3.2 ⟩
      rw [h1]

  rw [claim1]

  -- {m|m≡3[MOD 8]∧m≤2017}={3,11,..,2013+3}
  have claim2 : {m | m ≡ 3 [MOD 8] ∧ m ≤ 2017} =
    Finset.filter (fun m => m ≡ 3 [MOD 8]) (Finset.range 2018) := by
      ext m; simp [Nat.ModEq]; constructor <;> intro h <;> omega

  rw [claim2]
  rw [Set.ncard_eq_toFinset_card']
  simp
  decide -- or native_decide to avoid raising maxRecDepth