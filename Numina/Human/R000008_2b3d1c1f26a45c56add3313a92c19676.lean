import Mathlib
set_option maxHeartbeats 400000


/-Problem 8-/


lemma sum_swap : ∀ n : ℕ, ∀ f : (ℕ → ℕ → ℝ),
    (Finset.sum (Finset.range n) fun p => (Finset.sum (Finset.range (p + 1))) fun q => f p q) =
    (Finset.sum (Finset.range n) fun q => (Finset.sum (Finset.Icc q (n - 1)) fun p => f p q)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro f
    rw [Finset.sum_range_add, Finset.sum_range_one]
    simp only [add_zero]
    rw [ih f]
    nth_rw 2 [Finset.sum_range_add]
    rw [Finset.sum_range_one]
    simp [add_zero]
    rw [Finset.sum_range_add, Finset.sum_range_one, add_zero,← add_assoc, add_right_cancel_iff, 
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr
    · rfl
    · intro i
      simp
      intro hi
      have : n ∈ Finset.Icc i n := by simp; linarith
      symm
      rw [← Finset.sum_erase_add (Finset.Icc i n) (fun p => f p i) this]
      have : Finset.erase (Finset.Icc i n) n = Finset.Icc i (n - 1) := by
        rw [Finset.Icc_erase_right i n]
        ext x'
        simp
        intro _
        constructor
        intro hmp
        exact Nat.le_sub_one_of_lt hmp
        intro hmpr
        have : n - 1 < n := by apply Nat.sub_lt; linarith; norm_num
        linarith
      rw [this]


theorem int_val_poly : ∀ n : ℕ, ∀ f : (ℝ → ℝ), ∀ a : (Fin (n + 1) → ℝ), a n ≠ 0 →
    (∀ x : ℝ, f x = (Finset.sum (Finset.range (n + 1)) fun i => a i * x ^ i)) →
    (∃ b : Fin (n + 1) → ℤ, ∀ k : Fin (n + 1), f k = b k) →
    (∀ m : ℕ, ∃ t : ℤ, f m = t) := by
  intro n; induction n with
  | zero =>
    simp
    intro f a _ hf b hb m
    use b 0
    simp [← hb 0, hf m, hf 0]
  | succ n ih =>
    intro f a ha hf h'b m
    rcases h'b with ⟨b, hb⟩
    induction m with
    | zero => simp; use b 0; simp [← hb 0]
    | succ m ik =>
      rcases ik with ⟨t, ht⟩
      let g (x : ℝ) := f (x + 1) - f x
      let d (i : Fin (n + 1)) :=
      Finset.sum (Finset.range (n - i + 1)) fun j => a (n + 1 - j) * Nat.choose (n + 1 - j) i
      let d' (i : Fin (n + 1)) := b (i + 1) - b i
      have t0 : ∀ x : ℝ, g x = (Finset.sum (Finset.range (n + 1)) fun i => d i * x ^ i) := by
        intro x
        simp only [g, d]
        rw [hf (x + 1), hf x, ← Finset.sum_sub_distrib]
        simp only [add_comm (n + 1) 1]
        rw [Finset.sum_range_add, Finset.sum_range_one, pow_zero, pow_zero, sub_self, zero_add]
        simp only [add_pow, add_comm 1, one_pow, mul_one, ← mul_sub]
        have : ∀ i, (Finset.sum (Finset.range (i + 1 + 1)) fun x_2 => x ^ x_2 * ↑(Nat.choose (i + 1) x_2)) =
        (Finset.sum (Finset.range (i + 1)) fun x_2 => x ^ x_2 * ↑(Nat.choose (i + 1) x_2)) + x ^ (i + 1) := by
          intro i
          rw [Finset.sum_range_add]
          simp
        simp only [this, add_sub_cancel_right, Finset.mul_sum, Nat.sub_add_comm]
        rw [sum_swap (n + 1) (fun i j => a ↑(i + 1) * (x ^ j * ↑(Nat.choose (i + 1) j)))]
        apply Finset.sum_congr (by rfl)
        intro i hi
        have : Finset.Icc i (n + 1 - 1) = Finset.Icc i n := by congr
        rw [this, Finset.sum_mul]
        let w (l : ℕ) := if l ≤ n then (n - l) else l
        let v (l : ℕ) := a (n + 1 - l) * ↑(Nat.choose (n + 1 - l) i) * x ^ i
        have hw1 : ∀ l, l ∈ Finset.Icc i n ↔ w l ∈ Finset.range (n - ↑↑i + 1) := by
          simp only [w]
          intro l
          simp
          have t : i ≤ n := by simp at hi; apply Nat.lt_add_one_iff.mp; exact hi
          constructor
          · intro ⟨hl1, hl2⟩
            rw [if_pos hl2, Nat.lt_add_one_iff, Nat.sub_le_sub_iff_left t]
            exact hl1
          · split_ifs with hl1
            · intro hl2
              rw [Nat.lt_add_one_iff, Nat.sub_le_sub_iff_left t] at hl2
              exact ⟨hl2, hl1⟩
            · intro hl2
              push_neg at hl1
              rw [Nat.lt_add_one_iff] at hl2
              have t' : n - i ≤ n := by simp
              have : l ≤ n := le_trans hl2 t'
              linarith
        have hw2 : Function.Bijective w := by
          rw [Function.Bijective]
          constructor
          · rw [Function.Injective]
            intro a1 a2 h12
            simp only [w] at h12
            split_ifs at h12 with h1' h2'
            rw [Nat.sub_eq_iff_eq_add', ← Nat.add_sub_assoc] at h12
            symm at h12
            rw [Nat.sub_eq_iff_eq_add', Nat.add_right_cancel_iff] at h12
            exact h12
            have r1 : n ≤ a1 + n := by linarith
            exact le_trans h2' r1
            exact h2'
            exact h1'
            push_neg at h2'
            rw [symm h12] at h2'
            have r2 : n - a1 ≤ n := Nat.sub_le n a1
            linarith
            push_neg at h1'; rw [h12] at h1'
            have r3 : n - a2 ≤ n := Nat.sub_le n a2
            linarith
            exact h12
          · rw [Function.Surjective]
            intro b'
            simp only [w]
            cases Nat.lt_or_ge n b' with
            | inl hb' =>
              use b'
              split_ifs with hb''
              linarith
              rfl
            | inr hb' =>
              use n - b'
              split_ifs with hb''
              rw [Nat.sub_eq_iff_eq_add', Nat.sub_add_cancel]
              linarith
              exact hb''
              push_neg at hb''
              have s1 : n - b' ≤ n := Nat.sub_le n b'
              linarith
        have hw3 : ∀ i_1 ∈ Finset.Icc i n, a ↑(i_1 + 1) * (x ^ i * ↑(Nat.choose (i_1 + 1) i)) = v (w i_1) := by
          intro i1 hi1
          simp at hi1
          simp only [v, w, if_pos hi1.right]
          nth_rw 2 [mul_comm]
          rw [mul_assoc]
          have p1 : i1 + 1 = n + 1 - (n - i1) := by
            rw [Nat.sub_add_comm, Nat.sub_sub_eq_min]
            have : min n i1 = i1 := by simp; exact hi1.right
            rw [this]
            simp
          rw [← p1]
          have p2 : ↑(i1 + 1) = (n : Fin (n + 1 + 1)) + 1 - ↑(n - i1) := by
            rw [p1, Fin.ext_iff]
            simp
            rw [← p1]
            have q6 : n % (n + 1 + 1) = n := by apply Nat.mod_eq_of_lt; linarith
            have q2 : (n - i1) % (n + 1 + 1) = n - i1 := by
              apply Nat.mod_eq_of_lt
              rw [Nat.lt_add_one_iff,Nat.sub_le_iff_le_add, Nat.add_assoc]
              exact Nat.le_add_right n (1 + i1)
            have q1 : (↑(n - i1) : Fin (n + 1 + 1)) ≤ ((↑n + 1) : Fin (n + 1 + 1)) := by
              rw [Fin.le_def]
              simp
              rw [q2, Fin.val_add_one_of_lt]
              simp
              rw [q6]
              linarith
              rw [Fin.lt_def]
              simp
              rw [q6]; linarith
            rw [Fin.coe_sub_iff_le.mpr q1]
            simp
            have q3 : (i1 + 1) % (n + 1 + 1) = i1 + 1 := by
              apply Nat.mod_eq_of_lt
              rw [Nat.lt_add_one_iff, Nat.add_le_add_iff_right]; exact hi1.right
            rw [q2, q3]; symm; rw [Nat.sub_eq_iff_eq_add, p1, Nat.sub_add_cancel]
            rw [Fin.val_add_one_of_lt]
            simp
            linarith
            rw [Fin.lt_def]
            simp
            rw [q6]
            linarith
            have q4 : n - i1 ≤ n := Nat.sub_le n i1
            have q5 : n ≤ n + 1 := Nat.le_add_right n 1
            exact le_trans q4 q5
            rw [Fin.val_add_one_of_lt]
            simp
            rw [q6]
            linarith
            rw [Fin.lt_def]
            simp
            rw [q6]
            linarith
          rw [p2]
        rw [Finset.sum_bijective w hw2 hw1 hw3]
        apply Finset.sum_congr
        congr
        simp
        rw [Nat.mod_eq_of_lt]
        simp at hi; exact hi
        intro j _
        simp only [v]
        congr
        simp
        rw [Nat.mod_eq_of_lt]
        simp at hi
        exact hi
      have t1 : d (n : Fin (n + 1)) ≠ 0 := by
        simp only [d]
        simp
        push_neg
        constructor
        · have : (n : Fin (n + 1 + 1)) + 1 = ↑(n + 1) := by simp
          rw [this]
          exact ha
        · linarith
      have t2 : ∃ t : ℤ, g m = t := by
        apply ih g d t1 t0
        use d'
        intro k
        simp only [d', g]
        have t3 : ((k : Fin (n + 1 + 1)) : ℝ) = (k : ℝ) := by simp
        have t4 : k + (1 : ℝ) = ((k + 1) : Fin (n + 1 + 1)) := by simp
        nth_rw 2 [← t3]
        rw [hb k, t4, hb (k + 1)]
        simp
      rcases t2 with ⟨t', ht'⟩
      use t' + t
      simp [← ht, ← ht']
      ring
