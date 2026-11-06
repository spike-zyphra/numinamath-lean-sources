import Mathlib

/-a) Is it possible to colour the positive rational numbers with blue and red in a way that there are numbers of both colours and the sum of any two numbers of the same colour is the same colour as them?

Note: When forming a sum or a product, it is allowed to pick the same number twice.-/
theorem number_theory_8642_1 : ¬ ∃ (Red Blue : Set ℚ), Red ∩ Blue = ∅ ∧
Red ∪ Blue = {x | 0 < x } ∧ Red ≠ ∅ ∧ Blue ≠ ∅ ∧ (∀ x y, x ∈ Red → y ∈ Red → x+y ∈ Red) ∧
(∀ x y, x ∈ Blue → y ∈ Blue → x+y ∈ Blue) := by
-- We first rewrite our assumptions
  rintro ⟨R, B, hcap, hcup, hR0, hB0, hR, hB⟩
  let h'cup := hcup; rw [Set.ext_iff] at h'cup

-- Prove that the operation of taking a multiple or division is closed in $R$ or $B$
  have mula: ∀ n : ℕ, ∀ x ∈ R, 0 < n → (n : ℚ) * x ∈ R := by
    intro n' x hx; induction n' with
    | zero => simp_all
    | succ k ih =>
      simp_all; by_cases h' : k = 0; simp_all
      push_neg at h'; rw [← Nat.pos_iff_ne_zero] at h'; simp_all
      rw [add_mul, one_mul]; simp_all

  have mulb: ∀ n : ℕ, ∀ y ∈ B, 0 < n → (n : ℚ) * y ∈ B := by
    intro n' x hx; induction n' with
    | zero => simp_all
    | succ k ih =>
      simp_all; by_cases h' : k = 0; simp_all
      push_neg at h'; rw [← Nat.pos_iff_ne_zero] at h'; simp_all
      rw [add_mul, one_mul]; simp_all

  have mdR : ∀ a b : ℚ, 0 < a → 0 < b → (∃ n : ℕ, 0 < n ∧ b = (n : ℚ) * a) →
  (a ∈ R ↔ b ∈ R) := by
    rintro a b ha _ ⟨n, hn1, hn2⟩; constructor
    · intro h'; rw [hn2]
      apply mula; assumption; assumption
    intro h'; by_contra hneg
    have r1 : a ∈ B := by
      have := (h'cup a).mpr (show a ∈ {x | 0 < x} by simp; assumption)
      simp at this; cases this; contradiction; assumption
    have r2 := mulb n a r1 hn1
    rw [← hn2] at r2
    have : b ∈ R ∩ B := by simp; exact ⟨h', r2⟩
    rw [hcap] at this; contradiction

  have mdB : ∀ a b : ℚ, 0 < a → 0 < b → (∃ n : ℕ, 0 < n ∧ b = (n : ℚ) * a) →
  (a ∈ B ↔ b ∈ B) := by
    rintro a b ha _ ⟨n, hn1, hn2⟩; constructor
    · intro h'; rw [hn2]
      apply mulb; assumption; assumption
    intro h'; by_contra hneg
    have r1 : a ∈ R := by
      have := (h'cup a).mpr (show a ∈ {x | 0 < x} by simp; assumption)
      simp at this; cases this; assumption; contradiction
    have r2 := mula n a r1 hn1
    rw [← hn2] at r2
    have : b ∈ R ∩ B := by simp; exact ⟨r2, h'⟩
    rw [hcap] at this; contradiction
-- Split to two cases: $1$ belongs to $R$ or $1$ belongs to $B$
  have h1 := (h'cup 1).mpr (show (1:ℚ) ∈ {x | 0 < x } by simp)
  simp at h1; cases h1 with
  | inl hl =>
-- Case $1$ belongs to $R$, prove that $R$ has to be the whole set of positive rational numbers
-- which forces $B$ to be empty and this is a contradiction
    have alR : R = {x | 0 < x} := by
      ext x; constructor
      · intro hx; rw [← hcup]; simp; left; assumption
      simp; intro hx; let h'x := hx
      have hx1 := Rat.num_div_den x
      rw [← Rat.num_pos] at h'x
      have := Int.eq_ofNat_of_zero_le (show 0≤x.num by linarith)
      rcases this; rename_i p hp
      have denr := mula x.den 1 hl (show 0<x.den by rw [Nat.pos_iff_ne_zero]; apply Rat.den_ne_zero)
      simp at denr; rw [hp] at h'x; simp at h'x
      have numr := mula p 1 hl h'x
      simp at numr; rw [show (p:ℚ)=x.num by rw [hp];rfl] at numr
      have := mdR x x.num hx (show (0:ℚ)<x.num by simp; assumption)
      rw [this]; assumption; use x.den; constructor; apply Rat.den_pos
      nth_rw 3 [← hx1]; field_simp
    have : B = ∅ := by
      ext x; constructor
      · intro hx
        have : x ∈ R := by
          rw [alR, ← hcup]; simp; right; assumption
        rw [← hcap]; simp; exact ⟨this, hx⟩
      simp
    contradiction
-- Case $1$ belongs to $B$, prove that $B$ has to be the whole set of positive rational numbers
-- which forces $R$ to be empty and this is a contradiction
  | inr hr =>
    have alB : B = {x | 0 < x} := by
      ext x; constructor
      · intro hx; rw [← hcup]; simp; right; assumption
      simp; intro hx; let h'x := hx
      have hx1 := Rat.num_div_den x
      rw [← Rat.num_pos] at h'x
      have := Int.eq_ofNat_of_zero_le (show 0≤x.num by linarith)
      rcases this; rename_i p hp
      have denb := mulb x.den 1 hr (show 0<x.den by rw [Nat.pos_iff_ne_zero]; apply Rat.den_ne_zero)
      simp at denb; rw [hp] at h'x; simp at h'x
      have numr := mulb p 1 hr h'x
      simp at numr; rw [show (p:ℚ)=x.num by rw [hp];rfl] at numr
      have := mdB x x.num hx (show (0:ℚ)<x.num by simp; assumption)
      rw [this]; assumption; use x.den; constructor; apply Rat.den_pos
      nth_rw 3 [← hx1]; field_simp
    have : R = ∅ := by
      ext x; constructor
      · intro hx
        have : x ∈ B := by
          rw [alB, ← hcup]; simp; left; assumption
        rw [← hcap]; simp; exact ⟨hx, this⟩
      simp
    contradiction

/-
b) Is it possible to colour the positive rational numbers with blue and red in a way that there are numbers of both colours and the product of any two numbers of the same colour is the same colour as them?

Note: When forming a sum or a product, it is allowed to pick the same number twice.-/
theorem number_theory_8642_2 : ∃ (Red Blue : Set ℚ), Red ∩ Blue = ∅ ∧
Red ∪ Blue = {x | 0 < x } ∧ Red ≠ ∅ ∧ Blue ≠ ∅ ∧ (∀ x y, x ∈ Red → y ∈ Red → x*y ∈ Red) ∧
(∀ x y, x ∈ Blue → y ∈ Blue → x*y ∈ Blue) := by
-- Define $Red$ to be the set of positive rational numbers whose 2-adic valuation is nonnegtive
-- Define $Blue$ to be the set of positive rational numbers whose 2-adic valuation is negtive
  let Red : Set ℚ := {x | 0 < x ∧ 0 ≤ padicValRat 2 x}
  let Blue : Set ℚ := {x | 0 < x ∧ padicValRat 2 x < 0}
  use Red; use Blue; constructor
-- Check that Red intersects Blue is empty
  · ext x; simp [Red, Blue]; simp_all
  constructor
-- Check that Red unions Blue is the whole set of positive rational numbers
  · ext x; simp [Red, Blue]
    cases le_or_lt (0:ℤ) (padicValRat 2 x) with
    | inl h => simp_all
    | inr h => simp_all
  constructor
-- Check that Red and Blue are nonempty by exhibiting an element in each set
  · have : Nonempty Red := by
      use (2:ℚ)
      simp [Red]; rw [padicValRat_def]; simp
    intro neg; rw [neg] at this; simp at this
  constructor
  · have : Nonempty Blue := by
      use 1/(2:ℚ)
      simp [Blue]; rw [padicValRat_def]; simp
    intro neg; rw [neg] at this; simp at this
  constructor
-- Check Red and Blue are closed under multiplication
  · simp [Red]; intro x y hx1 hx2 hy1 hy2
    constructor
    · apply mul_pos; assumption; assumption
    rw [padicValRat.mul]; apply add_nonneg; assumption; assumption
    linarith; linarith
  simp [Blue]; intro x y hx1 hx2 hy1 hy2
  constructor
  · apply mul_pos; assumption; assumption
  rw [padicValRat.mul]; apply add_neg; assumption; assumption
  linarith; linarith