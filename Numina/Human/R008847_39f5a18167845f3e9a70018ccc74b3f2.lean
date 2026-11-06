import Mathlib

open Finset Real

/- 3. A3 (UKR) Let $n$ be an integer, $n \geq 3$. Let $a_{1}, a_{2}, \ldots, a_{n}$ be real numbers such that $2 \leq a_{i} \leq 3$ for $i=1,2, \ldots, n$. If $s=a_{1}+a_{2}+\cdots+a_{n}$, prove that  $$ \frac{a_{1}^{2}+a_{2}^{2}-a_{3}^{2}}{a_{1}+a_{2}-a_{3}}+\frac{a_{2}^{2}+a_{3}^{2}-a_{4}^{2}}{a_{2}+a_{3}-a_{4}}+\cdots+\frac{a_{n}^{2}+a_{1}^{2}-a_{2}^{2}}{a_{n}+a_{1}-a_{2}} \leq 2 s-2 n $$ -/
theorem inequalities_24641 {n : ℕ} (hn : 3 ≤ n) (a : ℕ → ℝ)
    (ha : ∀ i ∈ range n, 2 ≤ a i ∧ a i ≤ 3) (s : ℝ) (hs : s = ∑ i ∈ range n, a i) :
    ∑ i ∈ range n, ((a i)^2 + (a ((i + 1) % n))^2 - (a ((i + 2) % n))^2) /
    (a i + a ((i + 1) % n) - a ((i + 2) % n)) ≤ 2 * s - 2 * n := by
  -- range of a (i + 1) and a (i + 2)
  have hi1 {i : ℕ} : 2 ≤ a ((i + 1) % n) ∧ a ((i + 1) % n) ≤ 3 := by
    apply ha
    simp
    apply Nat.mod_lt (i + 1)
    exact Nat.zero_lt_of_lt hn
  have hi2 {i : ℕ} : 2 ≤ a ((i + 2) % n) ∧ a ((i + 2) % n) ≤ 3 := by
    apply ha
    simp
    apply Nat.mod_lt (i + 2)
    exact Nat.zero_lt_of_lt hn
  -- We will show that the denominator is nonzero.
  have hgt0 {i : ℕ} (hi : i ∈ range n) : 0 < a i + a ((i + 1) % n) - a ((i + 2) % n) := by
    calc
      a i + a ((i + 1) % n) - a ((i + 2) % n) ≥ 2 + 2 - 3 := by rel [(ha i hi).left, hi1.left, hi2.right]
      _ > 0 := by norm_num
  have hneq0 {i : ℕ} (hi : i ∈ range n) : a i + a ((i + 1) % n) - a ((i + 2) % n) ≠ 0 := by exact Ne.symm (ne_of_lt (hgt0 hi))
  -- Write $A_{i}=\frac{a_{i}^{2}+a_{i+1}^{2}-a_{i+2}^{2}}{a_{i}+a_{i+1}-a_{i+2}}=a_{i}+a_{i+1}+a_{i+2}-\frac{2 a_{i} a_{i+1}}{a_{i}+a_{i+1}-a_{i+2}}$.
  let Aᵢ := fun i => ((a i)^2 + (a ((i + 1) % n))^2 - (a ((i + 2) % n))^2) / (a i + a ((i + 1) % n) - a ((i + 2) % n))
  have simp_A {i : ℕ} (hi : i ∈ range n) : Aᵢ i = a i + a ((i + 1) % n) + a ((i + 2) % n) - 2 * a i * a ((i + 1) % n) / (a i + a ((i + 1) % n) - a ((i + 2) % n)) := by
    simp [Aᵢ]

    rw [div_eq_iff (hneq0 hi), sub_mul, add_mul, add_mul, div_mul_cancel₀ _ (hneq0 hi)]
    ring
  -- Since $2 a_{i} a_{i+1} \geq$ $4\left(a_{i}+a_{i+1}-2\right)$ (which is equivalent to $\left.\left(a_{i}-2\right)\left(a_{i+1}-2\right) \geq 0\right)$,
  have hmulge {i : ℕ} (hi : i ∈ range n) : 2 * a i * a ((i + 1) % n) ≥ 4 * (a i + a ((i + 1) % n) - 2) := by
    apply le_of_sub_nonneg
    calc
      0 ≤ 2 * (a i - 2) * (a ((i + 1) % n) - 2) := by
        apply mul_nonneg
        · apply mul_nonneg
          · norm_num
          · apply sub_nonneg.mpr (ha i hi).left
        · apply sub_nonneg.mpr hi1.left
      _ = 2 * a i * a ((i + 1) % n) - 4 * (a i + a ((i + 1) % n) - 2) := by ring
  -- because $1 \leq a_{i}+a_{i+1}-a_{i+2} \leq 4$.
  have hrange {i : ℕ} (hi : i ∈ range n) : 1 ≤ a i + a ((i + 1) % n) - a ((i + 2) % n) ∧ a i + a ((i + 1) % n) - a ((i + 2) % n) ≤ 4 := by
    constructor
    · calc
        1 = 2 + 2 - 3 := by norm_num
        _ ≤ a i + a ((i + 1) % n) - a ((i + 2) % n) := by rel [(ha i hi).left, hi1.left, hi2.right]
    · calc
        a i + a ((i + 1) % n) - a ((i + 2) % n) ≤ 3 + 3 - 2 := by rel [(ha i hi).right, hi1.right, hi2.left]
        _ = 4 := by norm_num
  -- it follows that $A_{i} \leq a_{i}+a_{i+1}+a_{i+2}-4\left(1+\frac{a_{i+2}-2}{a_{i}+a_{i+1}-a_{i+2}}\right) \leq a_{i}+a_{i+1}+a_{i+2}-$ $4\left(1+\frac{a_{i+2}-2}{4}\right)$
  have hAᵢle {i : ℕ} (hi : i ∈ range n) : Aᵢ i ≤ a i + a ((i + 1) % n) + a ((i + 2) % n) - 4 * (1 + (a ((i + 2) % n) - 2) / 4) := by
    rw [simp_A hi]
    apply sub_le_sub_left
    calc
      4 * (1 + (a ((i + 2) % n) - 2) / 4) ≤ 4 * (1 + (a ((i + 2) % n) - 2) / (a i + a ((i + 1) % n) - a ((i + 2) % n))) := by
        apply mul_le_mul_of_nonneg_left
        · simp
          apply div_le_div_of_nonneg_left
          · apply sub_nonneg.mpr hi2.left
          · calc
              0 < 1 := by norm_num
              _ ≤ a i + a ((i + 1) % n) - a ((i + 2) % n) := (hrange hi).left
          · exact (hrange hi).right
        · norm_num
      _ = 4 * (a i + a ((i + 1) % n) - 2) / (a i + a ((i + 1) % n) - a ((i + 2) % n)) := by
        rw [mul_div_assoc]
        congr
        rw [eq_div_iff (hneq0 hi), add_mul, div_mul_cancel₀ _ (hneq0 hi)]
        ring
      _ ≤  2 * a i * a ((i + 1) % n) / (a i + a ((i + 1) % n) - a ((i + 2) % n)) := by
        apply div_le_div_of_nonneg_right
        · exact hmulge hi
        · exact le_of_lt (hgt0 hi)
  -- Therefore $A_{i} \leq a_{i}+$ $a_{i+1}-2$
  have hAᵢle' {i : ℕ} (hi : i ∈ range n) : Aᵢ i ≤ a i + a ((i + 1) % n) - 2 := by
    calc
      Aᵢ i ≤ a i + a ((i + 1) % n) + a ((i + 2) % n) - 4 * (1 + (a ((i + 2) % n) - 2) / 4) := hAᵢle hi
      _ = a i + a ((i + 1) % n) - 2 := by ring
  -- so $\sum_{i=1}^{n} A_{i} \leq 2 s-2 n$ as required.
  have hsum : ∑ i in range n, Aᵢ i ≤ 2 * s - 2 * n := by
    calc
      ∑ i in range n, Aᵢ i ≤ ∑ i in range n, (a i + a ((i + 1) % n) - 2) := by
        apply sum_le_sum (fun i hi => hAᵢle' hi)
      _ = ∑ i in range n, a i + ∑ i in range n, a ((i + 1) % n) - 2 * n := by
        rw [sum_sub_distrib, sum_add_distrib, sum_const]
        simp [mul_comm]
      _ = s + s - 2 * n := by
        congr
        · simp [hs]
        · -- show ∑ i ∈ range n, a ((i + 1) % n) = ∑ i ∈ range n, a i
          rw [hs, eq_comm]
          let g : ℕ → ℕ := fun i => (i + 1) % n
          -- injectivity of g
          have he : ∀ x ∈ Finset.range n, ∀ y ∈ Finset.range n, g x = g y → x = y := by
            intro x hx y hy heq
            simp at hx hy
            simp [g] at heq
            by_cases h : x < n - 1
            · have : (x + 1) % n = x + 1 := by
                refine Nat.mod_eq_of_lt ?h
                exact Nat.add_lt_of_lt_sub h
              rw [this] at heq
              by_cases h' : y < n - 1
              · have : (y + 1) % n = y + 1 := by
                  refine Nat.mod_eq_of_lt ?h'
                  exact Nat.add_lt_of_lt_sub h'
                rw [this] at heq
                exact Nat.succ_injective heq
              · simp at h'
                have : (y + 1) % n = 0 := by apply Nat.mod_eq_zero_of_dvd ⟨1, ?_⟩; simp; exact Nat.le_antisymm hy h'
                simp [this] at heq
            · simp at h
              have hx : x + 1 = n := by apply Nat.le_antisymm hx h
              have : (x + 1) % n = 0 := by simp [hx]
              rw [this] at heq
              by_cases h' : y < n - 1
              · have : (y + 1) % n = y + 1 := by
                  refine Nat.mod_eq_of_lt ?_
                  exact Nat.add_lt_of_lt_sub h'
                simp [this] at heq
              · simp at h'
                have hy : y + 1 = n := by apply Nat.le_antisymm hy h'
                rw [←hy] at hx
                exact Nat.succ_inj'.mp hx
          -- calculate range of g
          have : (Finset.range n).image g = Finset.range n := by
            ext x
            constructor
            · intro hx
              simp [g] at hx
              obtain ⟨a, ⟨_, ha2⟩⟩ := hx
              rw [←ha2]
              simp
              apply Nat.mod_lt
              exact Nat.zero_lt_of_lt hn
            · intro hx
              simp [g]
              simp at hx
              by_cases h : x = 0
              · use n - 1
                constructor
                · simp; exact Nat.zero_lt_of_lt hn
                · rw [Nat.sub_add_cancel]
                  simp [h]
                  exact Nat.one_le_of_lt hn
              · use x - 1
                constructor
                · exact tsub_lt_of_lt hx
                · rw [Nat.sub_add_cancel]
                  exact Nat.mod_eq_of_lt hx
                  exact Nat.one_le_iff_ne_zero.mpr h
          nth_rw 1 [←this]
          -- now we can rewrite the sum
          rw [sum_image he]
      _ = 2 * s - 2 * n := by ring
  exact hsum
