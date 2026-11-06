import Mathlib

/-- a) Show that the last two decimal digits of a perfect square must be one of the following pairs: $\(00, e1, e4, 25, o6, e9\)$, where $\(e\)$ stands for any even digit and $\(o\)$ stands for any odd digit. (Hint: Show that $\(n^{2}, (50+n)^{2}\)$, and $\((50-n)^{2}\)$ all have the same final decimal digits, and then consider those integers $\(n\)$ with $\(0 \leq n \leq 25\)$.-/
theorem number_theory_4609 : ∀ n : Nat, (∃ m, Even m ∧ (n ^ 2 ≡ 10 * m + 1 [MOD 100] ∨
  n ^ 2 ≡ 10 * m + 4 [MOD 100] ∨ n ^ 2 ≡ 10 * m + 9 [MOD 100])) ∨ n ^ 2 ≡ 0 [MOD 100] ∨ n ^ 2 ≡ 25 [MOD 100] ∨
    (∃ m, Odd m ∧ n ^ 2 ≡ 10 * m + 6 [MOD 100]) := by
      intro n
      let k := n % 50
      -- prove $n^2 \equiv (n\%50)^2 [100]$ 
      have h1 : n ^ 2 ≡ k ^ 2 [MOD 100] := by
        have : n = n / 50 * 50+ n % 50 := Eq.symm (Nat.div_add_mod' n 50)
        rw [this]; ring_nf;
        have h1 : n / 50 * (n % 50) * 100 ≡ 0 [MOD 100] :=
          Nat.modEq_zero_iff_dvd.mpr (by norm_num)
        have h2 : (n / 50) ^ 2 * 2500 ≡ 0 [MOD 100] := by
          refine Nat.modEq_zero_iff_dvd.mpr (Dvd.dvd.mul_left (show 100 ∣ 2500 by decide) _)
        nth_rw 2 [show k ^ 2 = 0 + k ^ 2 by linarith]
        apply Nat.ModEq.add
        · exact Nat.ModEq.add h1 h2
        · simp [k]; rfl
      -- prove $n \% 50 < 50$.
      have hk : k < 50 := by simp [k]; exact Nat.mod_lt n (by linarith)
      have aux : ∀ a b, a ≡ b [MOD 100] → a ≡ b % 100 [MOD 100] := by
          intro a b h
          exact h.trans (by exact Nat.ModEq.symm (Nat.mod_modEq b 100))
      -- Classification discussion for $k$ less than 50
      interval_cases k
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; tauto
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨0, by simp [h1]⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨0, by simp [h1]⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨0, by simp [h1]⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; tauto
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; tauto
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; right; right; right; exact ⟨3, by simp [h1]; exact Nat.odd_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨4, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨6, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨8, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; tauto
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨2, by
        simp [h1];⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨4, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨6, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; right; right; right; exact ⟨9, by simp [h1]; exact Nat.odd_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; tauto
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; right; right; right; exact ⟨5, by simp [h1]; exact Nat.odd_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨8, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨2, by
        simp [h1]⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨6, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; tauto
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨4, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨8, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨2, by
        simp [h1]⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; right; right; right; exact ⟨7, by simp [h1]; exact Nat.odd_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; tauto
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; right; right; right; exact ⟨7, by simp [h1]; exact Nat.odd_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨2, by
        simp [h1]⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨8, by
      simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨4, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; tauto
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨6, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨2, by
        simp [h1]⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨8, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; right; right; right; exact ⟨5, by simp [h1]; exact Nat.odd_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; tauto
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; right; right; right; exact ⟨9, by simp [h1]; exact Nat.odd_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨6, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨4, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨2, by
        simp [h1];⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; tauto
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨8, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨6, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨4, by
        simp [h1]; exact Nat.even_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; right; right; right; exact ⟨3, by simp [h1]; exact Nat.odd_iff.mpr rfl⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; tauto
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; tauto
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨0, by simp [h1]⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨0, by simp [h1]⟩
      · replace h1 := aux (n ^ 2) _ h1; simp at h1; exact Or.inl ⟨0, by simp [h1]⟩
