import Mathlib

/-
PROBLEM:
Find the smallest positive integer whose cube ends in 888888.
-/

theorem number_theory_95385 :
IsLeast {n : ℕ | 0 < n ∧ (n^3) % 1000 = 888} 192 := by {
  rw [IsLeast]
  constructor
  -- Show that 192 satisfies the condiction (trivial)
  simp
  -- Show that any number that satisies the condition is ≥ 192
  rw [mem_lowerBounds]
  intro n
  simp
  intro h
  intro hn
  have hn' := hn
  -- Show that we must have n % 10 = 2 by case distinction
  let k := n % 10
  have hk3 : k^3 % 10 = 8 := by {
    unfold k
    rw [←Nat.pow_mod]
    have : 10 ∣ 1000 := by trivial
    rw [←Nat.mod_mod_of_dvd (n^3) this]
    rw [hn]
  }
  have hkmod10 : k = 2 := by {
    have : k < 10 := by apply Nat.mod_lt; trivial
    match k with
    | 0 => contradiction
    | 1 => contradiction
    | 2 => trivial
    | 3 => contradiction
    | 4 => contradiction
    | 5 => contradiction
    | 6 => contradiction
    | 7 => contradiction
    | 8 => contradiction
    | 9 => contradiction
  }
  unfold k at hkmod10
  have hnm: ∃ m : ℕ, n = 10*m+2 := by {
    rw [Nat.mod_def] at hkmod10
    use (n / 10)
    rw [←hkmod10, ←Nat.add_sub_assoc, Nat.add_sub_cancel_left]
    exact Nat.mul_div_le n 10
  }
  rcases hnm with ⟨m,hm⟩
  rw [hm] at hn
  ring_nf at hn
  simp at hn

  -- Show that we must have n % 100 = 42 or 92 by case distinction
  let l := m % 10
  have hnmod100 : n % 100 = 10*l+2 := by {
    unfold l
    rw [hm, Nat.add_mod]
    have : 100 = 10*10 := by trivial
    conv in 100 => rw [this]
    rw [Nat.mul_mod_mul_left]
    apply Nat.mod_eq_of_lt
    simp
    have : (m % 10 < 10) := by apply Nat.mod_lt; trivial
    linarith
  }
  have hlmod10 : l = 4 ∨ l = 9 := by {
    have hn3mod100 : n^3 % 100 = 88 := by {
      have : 100 ∣ 1000 := by trivial
      rw [←Nat.mod_mod_of_dvd _ this, hn']
    }
    have : l < 10 := by apply Nat.mod_lt; trivial
    match l with
    | 0 => {
      simp at hnmod100
      rw [Nat.pow_mod, hnmod100] at hn3mod100
      contradiction
    }
    | 1 => {
      simp at hnmod100
      rw [Nat.pow_mod, hnmod100] at hn3mod100
      contradiction
    }
    | 2 => {
      simp at hnmod100
      rw [Nat.pow_mod, hnmod100] at hn3mod100
      contradiction
    }
    | 3 => {
      simp at hnmod100
      rw [Nat.pow_mod, hnmod100] at hn3mod100
      contradiction
    }
    | 4 => trivial
    | 5 => {
      simp at hnmod100
      rw [Nat.pow_mod, hnmod100] at hn3mod100
      contradiction
    }
    | 6 => {
      simp at hnmod100
      rw [Nat.pow_mod, hnmod100] at hn3mod100
      contradiction
    }
    | 7 => {
      simp at hnmod100
      rw [Nat.pow_mod, hnmod100] at hn3mod100
      contradiction
    }
    | 8 => {
      simp at hnmod100
      rw [Nat.pow_mod, hnmod100] at hn3mod100
      contradiction
    }
    | 9 => trivial
  }
  have hnmod100eq : n % 100 = 42 ∨ n % 100 = 92 := by {
    cases hlmod10 with
    | inl hl4 => {
      rw [hnmod100, hl4]
      trivial
    }
    | inr hl9 => {
      rw [hnmod100, hl9]
      trivial
    }
  }

  -- Check the remaining cases by hand and conclude
  have hnn42 : n ≠ 42 := by {
    intro hn42
    rw [hn42] at hn'
    contradiction
  }
  have hnn92 : n ≠ 92 := by {
    intro hn92
    rw [hn92] at hn'
    contradiction
  }
  have hnn142 : n ≠ 142 := by {
    intro hn142
    rw [hn142] at hn'
    contradiction
  }
  cases hnmod100eq with
  | inl hnmod10042 => {
    have hna: ∃ a : ℕ, n = 100*a+42 := by {
      rw [Nat.mod_def] at hnmod10042
      use (n / 100)
      rw [←hnmod10042, ←Nat.add_sub_assoc, Nat.add_sub_cancel_left]
      exact Nat.mul_div_le n 100
    }
    rcases hna with ⟨a,ha⟩
    cases a with
    | zero => {
      simp at ha
      contradiction
    }
    | succ a => {
      cases a with
      | zero => {
        simp at ha
        contradiction
      }
      | succ a => {
        linarith
      }
    }
  }
  | inr hnmod10092 => {
    have hna: ∃ a : ℕ, n = 100*a+92 := by {
      rw [Nat.mod_def] at hnmod10092
      use (n / 100)
      rw [←hnmod10092, ←Nat.add_sub_assoc, Nat.add_sub_cancel_left]
      exact Nat.mul_div_le n 100
    }
    rcases hna with ⟨a,ha⟩
    cases a with
    | zero => {
      simp at ha
      contradiction
    }
    | succ a => {
      linarith
    }
  }
}