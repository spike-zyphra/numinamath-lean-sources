import Mathlib

open scoped Cardinal

/-- Define the set of divisors of integer n-/
def Int.divisors (n : ℤ) : Finset ℤ :=
  (Nat.divisors (natAbs n) |>.image fun x : ℕ => x) ∪
  (Nat.divisors (natAbs n) |>.image (fun x : ℕ => -x))

/-- Auxiliary lemma : $x$ is divisor of integer $n$ if and only if $x$ divides $n$.-/
lemma Int.mem_divisors {n : ℤ} (hn : n ≠ 0) (x : ℤ) : x ∈ n.divisors ↔ x ∣ n := by
  simp only [Int.divisors, Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
  apply Iff.intro
  · rintro (⟨a, ⟨⟨h₁, _⟩, h₃⟩⟩ | ⟨a, ⟨⟨h₁, _⟩, h₃⟩⟩) <;>
    · rw [← h₃, ← Int.natAbs_dvd_natAbs]
      simpa using h₁
  · intro h
    rw [← Int.natAbs_dvd_natAbs] at h
    by_cases hx : 0 <= x
    · refine .inl ⟨x.natAbs, ⟨⟨h, ?_⟩, by simpa⟩⟩
      simpa using hn
    · refine .inr ⟨x.natAbs, ⟨⟨h, ?_⟩, by
        rw [Int.ofNat_natAbs_of_nonpos (by linarith)]; linarith⟩⟩
      simpa using hn

def HasOnlyIntegers (x : Set ℝ) := x.Nonempty ∧ x ⊆ Set.range Int.cast

/-- Auxiliary lemma : There is at most one such pair $(r,s)$ that $r \leq s$ 
    and $r + s = a$ and $r * s = b$ where $a$ and $b$ are real numbers.-/
lemma unique_lemma_1 {a b : ℝ} :
    Subsingleton {(r, s) : ℝ × ℝ | r ≤ s ∧ r + s = a ∧ r * s = b} := by
  constructor
  intro ⟨⟨r, s⟩, ⟨h₁, h₂, h₃⟩⟩ ⟨⟨r', s'⟩, ⟨h₁', h₂', h₃'⟩⟩
  congr 1
  rw [← h₂'] at h₂
  rw [← h₃'] at h₃
  clear h₂' h₃'
  have h : (r - s) ^ 2 = (r' - s') ^ 2 := calc
    _ = (r + s) ^ 2 - 4 * (r * s) := by ring
    _ = (r' + s') ^ 2 - 4 * (r' * s') := by rw [h₂, h₃]
    _ = _ := by ring
  rw [sq_eq_sq_iff_eq_or_eq_neg] at h
  cases' h <;> ext <;> linarith

/-- For how many real numbers $a$ does the quadratic equation $x^2 + ax + 6a=0$ have only integer roots for $x$? -/
theorem intermediate_algebra_4075 : #{a | HasOnlyIntegers {x | x ^ 2 +  a * x + 6 * a = 0}} = 10 := by
  -- According to above lemma, the equation $x ^ 2 + a * x + 6 * a = 0$ has at most one pair $(r,s)$ such that $r$ and $s$ are both its roots.
  set X := {a | HasOnlyIntegers {x | x ^ 2 + a * x + 6 * a = 0}}
  have f {a} (ha : a ∈ X) : {(r, s) : ℤ × ℤ | r ≤ s ∧ r + s = -a ∧ r * s = 6 * a} := by
    rcases ha with ⟨h, h'⟩
    choose r hr using h
    have hr₁ : r * r - (-a) * r + 6 * a = 0 := by simp at hr; linarith
    choose s hs using vieta_formula_quadratic hr₁
    choose r' hr' using h' hr
    choose s' hs' using h' (show s ^ 2 + a * s + 6 * a = 0 by linarith)
    let u := min r' s'
    let v := max r' s'
    exact ⟨⟨u, v⟩, by simp [u, v], by simpa [u, v, hr', hs'] using hs.2⟩
  -- use the transitivity to change the goal to `#{(r, s) : ℤ × ℤ | r ≤ s ∧ (r + 6) * (s + 6) = 36}` = 10
  transitivity #{(r, s) : ℤ × ℤ | r ≤ s ∧ (r + 6) * (s + 6) = 36}
  · let p (r s : ℤ) := r ≤ s ∧ (r + 6) * (s + 6) = 36
    let r' {a} (ha : a ∈ X) := (f ha).1.1
    let s' {a} (ha : a ∈ X) := (f ha).1.2
    let inv (r s : ℤ) : ℝ := -(r + s)
    have p_r's' {a} (ha : a ∈ X) : p (r' ha) (s' ha) := by
      simp only [r', s']
      have h := (f ha).2
      simp only [Set.mem_setOf_eq] at h
      set x := (f ha).1.1
      set y := (f ha).1.2
      refine ⟨h.1, ?_⟩
      rw [← sub_eq_zero]
      calc
        _ = x * y + 6 * (x + y) := by ring
        _ = _ := by rify; rw [h.2.1, h.2.2]; linarith
    have inv_eq {a} (ha : a ∈ X) : inv (r' ha) (s' ha) = a := by
      have : r' ha + s' ha = -a := (f ha).2.2.1
      simp only [inv]
      linarith
    -- if $r,s$ satisfy `r ≤ s ∧ (r + 6) * (s + 6) = 36`, then $-(r+s)$ also in `X`.
    have inv_mem {r s : ℤ} (hrs : p r s) : inv r s ∈ X := by
      simp [X]
      refine Eq.mpr (β := HasOnlyIntegers {x | (x - r) * (x - s) = 0}) ?_ ?_
      · congr! 4 with x
        replace hrs := hrs.2
        rify at hrs
        rw [← sub_eq_zero] at hrs ⊢
        rw [← neg_eq_zero]
        exact Eq.trans (by ring) hrs
      · simp only [mul_eq_zero, HasOnlyIntegers]
        refine ⟨⟨r, by simp⟩, fun x hx => ?_⟩
        simp only [Set.mem_setOf_eq] at hx
        cases hx
        · simpa using ⟨r, by linarith⟩
        · simpa using ⟨s, by linarith⟩
    have rs_inv {r s : ℤ} (hrs : p r s) : (r' (inv_mem hrs), s' (inv_mem hrs)) = (r, s) := by
      have h := p_r's' (inv_mem hrs)
      set a := r' (inv_mem hrs)
      set b := s' (inv_mem hrs)
      have h₁ : - (a + b) = - (r + s) := by rify; exact inv_eq <| inv_mem hrs
      replace h₁ : a + b = r + s := by linarith
      simp only [p] at hrs h
      have h₂ : a * b = r * s := calc
        _ = (a + 6) * (b + 6) - 6 * (a + b) - 36 := by ring
        _ = - 6 * (r + s) := by rw [h.2, h₁]; ring
        _ = (r + 6) * (s + 6) - 6 * (r + s) - 36 := by rw [hrs.2]; ring
        _ = _ := by ring
      have hrs' := hrs.1; have h' := h.1
      rify at hrs'; rify at h'; rify at h₁; rify at h₂
      have := unique_lemma_1.elim ⟨⟨a, b⟩, ⟨h', h₁, h₂⟩⟩ ⟨⟨r, s⟩, ⟨hrs', rfl, rfl⟩⟩
      simpa
    apply Cardinal.mk_congr
    -- Prove `X ≃ {(r, s) | r ≤ s ∧ (r + 6) * (s + 6) = 36}` using the bijective of function `fun ⟨a, ha⟩ => ⟨⟨r' ha, s' ha⟩, p_r's' ha⟩` from `X` to `{(r, s) | r ≤ s ∧ (r + 6) * (s + 6) = 36}`.
    apply Equiv.ofBijective fun ⟨a, ha⟩ => ⟨⟨r' ha, s' ha⟩, p_r's' ha⟩
    constructor
    · apply Function.HasLeftInverse.injective
      use fun ⟨⟨r, s⟩, hrs⟩ => ⟨inv r s, inv_mem hrs⟩
      intro ⟨a, ha⟩
      simpa only [Subtype.mk.injEq] using inv_eq ha
    · intro ⟨⟨r, s⟩, hrs⟩
      use ⟨inv r s, inv_mem hrs⟩
      simpa using rs_inv hrs
  · calc
    _ = #(Int.divisors 36
        |>.image (fun r => (r - 6, 36 / r - 6))
        |>.filter (fun x => x.1 <= x.2)) := by
      congr 2
      refine funext (fun ⟨r, s⟩ => ?_)
      simp only [Finset.filter_val, Finset.image_val, Multiset.mem_filter, Multiset.mem_dedup,
        Multiset.mem_map, Finset.mem_val, Prod.mk.injEq, eq_iff_iff]
      refine ⟨fun ⟨p, q⟩ => ⟨⟨r + 6, ⟨?_, ?_, ?_⟩⟩, p⟩, fun ⟨p, q⟩ => ⟨q, ?_⟩⟩
      · rw [Int.mem_divisors (by norm_num)]
        exact ⟨s + 6, q.symm⟩
      · simp
      · rw [← q, Int.mul_ediv_cancel_left]
        · simp
        · intro h'; simp [h'] at q
      · rcases p with ⟨a, ha₁, ha₂, ha₃⟩
        rw [← ha₂, ← ha₃]
        simpa using Int.mul_ediv_cancel' (by rwa [← Int.mem_divisors (by norm_num)])
    _ = Finset.card (Int.divisors 36
        |>.image (fun r => (r - 6, 36 / r - 6))
        |>.filter (fun x => x.1 <= x.2)) := by rw [Cardinal.mk_coe_finset]
    -- Here we use the computed properties of `Int.divisors`, `Finset.image`, and `Finset.filter` to let the Lean system automatically enumerate the number of elements (10)
    _ = 10 := by rfl
