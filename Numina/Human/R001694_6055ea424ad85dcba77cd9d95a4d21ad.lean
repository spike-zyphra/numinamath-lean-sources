import Mathlib

/- 25. N2 (RUS) The function $\psi$ from the set $\mathbb{N}$ of positive integers into itself is defined by the equality  $$ \psi(n)=\sum_{k=1}^{n}(k, n), \quad n \in \mathbb{N} $$  where $(k, n)$ denotes the greatest common divisor of $k$ and $n$. (a) Prove that $\psi(m n)=\psi(m) \psi(n)$ for every two relatively prime $m, n \in$ $\mathbb{N}$. (b) Prove that for each $a \in \mathbb{N}$ the equation $\psi(x)=a x$ has a solution. (c) Find all $a \in \mathbb{N}$ such that the equation $\psi(x)=a x$ has a unique solution. -/
def ψ : ℕ → ℕ := fun n => ∑ k ∈ Finset.Icc 1 n, Nat.gcd k n
-- Prove that ψ(n) = ∑_{d ∣ n} ϕ(d) * n / d. This is used in each of the below theorems.
lemma hψ (n : ℕ) (npos : 0 < n) : ψ n = ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d ∣ n), d.totient * (n / d) := by
  -- Show that gcd(n, k) ∈ (0, n].
  have h₀ {n k : ℕ} (npos : 0 < n) : Nat.gcd k n ∈ Finset.Ioc 0 n := by
    simp
    refine ⟨by apply Nat.gcd_pos_of_pos_right k npos, by apply Nat.gcd_le_right n npos⟩
  -- Define embedding (injective function) s mapping divisor d of n to n / d.
  let s : n.divisors ↪ n.divisors := ⟨fun d => ?_, fun d₁ d₂ heq => ?_⟩
  pick_goal 2
  . -- Assign the value n / d to d and show that mapping d ↦ n / d is well-defined.
    use n / d
    obtain ⟨d, hd⟩ := d
    simp [show ¬n = 0 by omega] at hd ⊢
    exact Nat.div_dvd_of_dvd hd
  pick_goal 2
  . -- Show that the mapping s is injective.
    obtain ⟨d₁, h₁⟩ := d₁
    obtain ⟨d₂, h₂⟩ := d₂
    have hd₁ := h₁
    have hd₂ := h₂
    simp at heq d₁ d₂ ⊢
    simp [show ¬n = 0 by omega] at h₁ h₂
    rw [dvd_iff_exists_eq_mul_left] at h₁ h₂
    obtain ⟨m₁, h₁⟩ := h₁
    obtain ⟨m₂, h₂⟩ := h₂
    nth_rewrite 1 [h₁] at heq
    nth_rewrite 1 [h₂] at heq
    rw [Nat.mul_div_cancel, Nat.mul_div_cancel] at heq
    calc
      d₁ = m₁ * d₁ / m₁ := by rw [Nat.mul_div_cancel_left]; by_contra!; rw [show m₁ = 0 by omega] at h₁; linarith only [npos, h₁]
      _ = m₂ * d₂ / m₂ := by rw [<-h₁, heq, h₂]
      _ = d₂ := by rw [Nat.mul_div_cancel_left]; by_contra!; rw [show m₂ = 0 by omega] at h₂; linarith only [npos, h₂]
    all_goals
      apply Nat.pos_of_mem_divisors at hd₁
      apply Nat.pos_of_mem_divisors at hd₂
      assumption
  -- Show that s is surjective.
  have ssurj : Function.Surjective s := by
    simp only [Function.Surjective]
    intro d
    use s d
    obtain ⟨d, hd⟩ := d
    simp [s]
    rw [Nat.div_div_self]
    simp [Nat.divisors] at hd
    tauto
    omega
  have hcard (d : ℕ) : d ∈ n.divisors → ((Finset.Icc 1 n).filter (fun k => n / d = Nat.gcd k n)).card = d.totient := by
    intro hd
    rw [Nat.totient_eq_card_coprime]
    -- Define embedding (injective function) t from {k | gcd(k, n) = n / d} to {k | 0 ≤ k < d ∧ k ⟂ d}.
    let t : (Finset.Icc 1 n).filter (fun k => n / d = Nat.gcd k n) ↪ (Finset.range d).filter (d.Coprime) := ⟨fun k => ?_, fun k₁ k₂ heq => ?_⟩
    pick_goal 2
    . -- Assign the value of the mapping and show that it is well-defined.
      obtain ⟨k, hk⟩ := k
      simp at hk
      have h₁ : n / d ∣ k := by
        rw [hk.2]
        exact Nat.gcd_dvd_left k n
      rw [dvd_iff_exists_eq_mul_left] at h₁
      use if k = n then 0 else k / (n / d) -- The convention adopted in the definition of totient function takes numbers from 0 to d - 1 (inclusive), not 1 to d.
      obtain ⟨c, h₁⟩ := h₁
      have h₃ : n = d * (n / d) := by
        rw [Nat.mul_comm, Nat.div_mul_cancel]
        simp at hd
        tauto
      by_cases h₂ : k = n
      . simp [h₂]
        rw [h₂, Nat.gcd_self] at hk
        replace hk := hk.2
        replace hk : d = 1 := by
          rw [Nat.div_eq_self] at hk
          simp [show n ≠ 0 by omega] at hk
          exact hk
        omega
      . simp [h₂]
        rw [h₁, Nat.mul_div_cancel]
        refine ⟨?_, ?_⟩
        . by_contra!
          replace this : k ≥ n := by
            calc
              k = c * (n / d) := h₁
              _ ≥ n := by nth_rewrite 2 [h₃]; apply Nat.mul_le_mul_right; exact this
          omega
        nth_rewrite 3 [h₁] at hk
        nth_rewrite 4 [h₃] at hk
        obtain ⟨h₄, h₅⟩ := hk
        symm at h₅
        rw [Nat.gcd_mul_right, Nat.mul_left_eq_self_iff, Nat.gcd_comm] at h₅
        simp [Nat.Coprime, h₅]
        all_goals
          by_contra! h₆
          replace h₆ : n / d = 0 := by
            omega
          rw [h₆] at h₃
          omega
    pick_goal 2
    . -- Show that the mapping t is injective.
      obtain ⟨k₁, h₁⟩ := k₁
      obtain ⟨k₂, h₂⟩ := k₂
      simp at heq ⊢
      by_cases h₃ : k₁ = n
      . by_cases h₄ : k₂ = n
        . omega
        . simp [h₃, h₄] at heq
          simp at h₂
          have h₅ := h₂.2
          replace h₅ : n / d ∣ k₂ := by
            rw [h₅]
            apply Nat.gcd_dvd_left
          rw [dvd_iff_exists_eq_mul_left] at h₅
          obtain ⟨c, h₅⟩ := h₅
          rw [h₅, Nat.mul_div_cancel] at heq
          rw [<-heq] at h₅
          omega
          by_contra!
          replace this : n / d = 0 := by
            omega
          rw [this] at h₅
          omega
      . by_cases h₄ : k₂ = n
        . simp only [h₃, ↓reduceIte, h₄] at heq
          simp at h₁
          have h₅ := h₁.2
          replace h₅ : n / d ∣ k₁ := by
            rw [h₅]
            apply Nat.gcd_dvd_left
          rw [dvd_iff_exists_eq_mul_left] at h₅
          obtain ⟨c, h₅⟩ := h₅
          rw [h₅, Nat.mul_div_cancel] at heq
          rw [heq] at h₅
          omega
          by_contra!
          replace this : n / d = 0 := by
            omega
          rw [this] at h₅
          omega
        . simp [h₃, h₄] at heq
          calc
            k₁ = k₁ / (n / d) * (n / d) := by rw [Nat.div_mul_cancel]; simp at h₁; rw [h₁.2]; apply Nat.gcd_dvd_left
            _ = k₂ / (n / d) * (n / d) := by rw [heq]
            _ = k₂ := by rw [Nat.div_mul_cancel]; simp at h₂; rw [h₂.2]; apply Nat.gcd_dvd_left
    -- Show that t is surjective.
    have tsurj : Function.Surjective t := by
      simp only [Function.Surjective]
      intro l
      obtain ⟨l, hl⟩ := l
      simp at hl ⊢
      use if l = 0 then n else l * (n / d)
      by_cases h₂ : l = 0
      . simp [h₂, t]
        rw [h₂] at hl
        replace hl : d = 1 := by
          rw [<-Nat.coprime_zero_right]
          tauto
        rw [hl]
        omega
      . simp at hd
        obtain ⟨h₃, h₄⟩ := hd
        have hd := h₃
        rw [dvd_iff_exists_eq_mul_left] at h₃
        obtain ⟨c, h₃⟩ := h₃
        have h₅ : 0 < l := by
          omega
        have h₆ : 0 < n / d := by
          rw [h₃, Nat.mul_div_cancel]
          by_contra!
          replace this : c = 0 := by
            omega
          rw [this] at h₃
          omega
          exact lt_trans h₅ hl.1
        replace h₃ : 0 < l * (n / d) := by
          positivity
        have h₇ : l * (n / d) < n := by
          calc
            l * (n / d) < d * (n / d) := by rw [Nat.mul_lt_mul_right]; exact hl.1; exact h₆
            _ = n := by rw [Nat.mul_comm, Nat.div_mul_cancel]; exact hd
        simp [h₂, t, show 1 ≤ l * (n / d) by omega, show l * (n / d) ≤ n by omega, show l * (n / d) ≠ n by omega]
        nth_rewrite 3 [show n = d * (n / d) by rw [Nat.mul_comm, Nat.div_mul_cancel]; exact hd]
        refine ⟨?_, by apply Nat.mul_div_cancel; exact h₆⟩
        symm
        rw [Nat.gcd_mul_right, Nat.mul_left_eq_self_iff, Nat.gcd_comm]
        exact hl.2
        exact h₆
    nth_rewrite 2 [<-Finset.card_attach]
    rw [show ((Finset.range d).filter (d.Coprime)).attach = (Finset.map t Finset.univ) by rw [Finset.map_univ_of_surjective tsurj, Finset.attach_eq_univ]]
    rw [Finset.card_map]
    simp
  calc
    ψ n = ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Ioc 0 n, if d = Nat.gcd k n then d else 0 := by dsimp [ψ]; congr; ext k; simp [Finset.sum_ite_eq', h₀ npos]
    _ = ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ (Finset.Ioc 0 n).filter (fun d => d ∣ n), if d = Nat.gcd k n then d else 0 := by simp [Finset.sum_filter, h₀ npos]; congr; ext k; simp [Nat.gcd_dvd_right]
    _ = ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n), if d = Nat.gcd k n then d else 0 := by congr
    _ = ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ n.divisors, if n / d = Nat.gcd k n then n / d else 0 := by congr; ext k; rw [<-Finset.sum_attach n.divisors]; rw [show n.divisors.attach = Finset.map s Finset.univ by rw [Finset.map_univ_of_surjective ssurj, Finset.attach_eq_univ]]; rw [Finset.sum_map Finset.univ s]; simp only [<-Finset.attach_eq_univ]; rw [<-Nat.divisors]; rw [<-Finset.sum_attach n.divisors]; dsimp [s]; congr; ext d; rw [Nat.div_div_self]; obtain ⟨d, hd⟩ := d; simp at hd; simp [hd.1]; omega
    _ = ∑ d ∈ n.divisors, ∑ _ ∈ (Finset.Icc 1 n).filter (fun k => n / d = Nat.gcd k n), n / d := by rw [Finset.sum_comm]; congr; ext d; rw [Finset.sum_filter]
    _ = ∑ d ∈ (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n), d.totient * (n / d) := by rw [<-Nat.divisors]; apply Finset.sum_congr; rfl; intro d; intro hd; rw [<-hcard, <-Finset.sum_const_nat]; intro k _; rfl; exact hd
    _ = ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d ∣ n), d.totient * (n / d) := by congr

/- (a) Prove that $\psi(m n)=\psi(m) \psi(n)$ for every two relatively prime $m, n \in$ $\mathbb{N}$. -/
theorem number_theory_25179_1 (m n : ℕ) (mpos : 0 < m) (npos : 0 < n) (h : Nat.Coprime m n): ψ (m * n) = ψ m * ψ n := by
-- Define embedding (injective function) ϕ mapping divisor f of mn to (d, e), where d ∣ n and e ∣ m.
let ϕ : (Finset.Icc 1 (m * n)).filter (fun f => f ∣ (m * n)) ↪ ((Finset.Icc 1 n).filter (fun d => d ∣ n) ×ˢ (Finset.Icc 1 m).filter (fun e => e ∣ m)) := ⟨fun f => ⟨⟨Nat.gcd f n, Nat.gcd f m⟩, ?_⟩, ?_⟩
-- Show that the mapping is well-defined.
pick_goal 2
. rw [Nat.Coprime, Nat.gcd_comm] at h
  obtain ⟨f, hf⟩ := f
  simp at hf ⊢
  obtain ⟨⟨hf, _⟩, _⟩ := hf
  refine ⟨⟨⟨by apply Nat.gcd_pos_of_pos_left n hf, by apply Nat.gcd_le_right n npos⟩, by apply Nat.gcd_dvd_right⟩, ⟨⟨by apply Nat.gcd_pos_of_pos_left m hf, by apply Nat.gcd_le_right m mpos⟩, by apply Nat.gcd_dvd_right⟩⟩
-- Prove that ϕ is injective.
pick_goal 2
. simp [Function.Injective]
  intro f _ _ hf g _ _ hg hfg₁ hfg₂
  calc
    f = Nat.gcd f (m * n) := by symm; apply Nat.gcd_eq_left; exact hf
    _ = Nat.gcd f m * Nat.gcd f n := by apply Nat.Coprime.gcd_mul; exact h
    _ = Nat.gcd g m * Nat.gcd g n := by rw [hfg₁, hfg₂]
    _ = Nat.gcd g (m * n) := by symm; apply Nat.Coprime.gcd_mul; exact h
    _ = g := by apply Nat.gcd_eq_left; exact hg
-- Show that ϕ is surjective.
have ϕsurj : Function.Surjective ϕ := by
  simp only [Function.Surjective]
  intro ⟨⟨d, e⟩, hde⟩
  use ⟨d * e, ?_⟩
  pick_goal 2
  . simp at hde ⊢
    refine ⟨⟨by nlinarith only [hde.1.1.1, hde.2.1.1], by nlinarith only [hde.1.1.2, hde.2.1.2]⟩, by rw [mul_comm]; apply Nat.mul_dvd_mul hde.2.2 hde.1.2⟩
  simp [ϕ]
  simp at hde
  rw [Nat.Coprime, Nat.gcd_comm] at h
  have h₁ : Nat.Coprime d e := by
    rw [Nat.Coprime, <-Nat.dvd_one, <-h]
    calc
      Nat.gcd d e ∣ Nat.gcd n e := by apply Nat.gcd_dvd_gcd_of_dvd_left; exact hde.1.2
      _ ∣ Nat.gcd n m := by apply Nat.gcd_dvd_gcd_of_dvd_right; exact hde.2.2
  refine ⟨?_, ?_⟩
  all_goals
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul]
    pick_goal 2
    . apply h₁
  . rw [show Nat.gcd n e = 1 by rw [<-Nat.dvd_one, <-h]; apply Nat.gcd_dvd_gcd_of_dvd_right; apply hde.2.2]
    simp
    apply Nat.gcd_eq_right hde.1.2
  . rw [show Nat.gcd m d = 1 by rw [<-Nat.dvd_one, <-h, Nat.gcd_comm n m]; apply Nat.gcd_dvd_gcd_of_dvd_right; apply hde.1.2]
    simp
    apply Nat.gcd_eq_right hde.2.2
calc
  ψ (m * n) = ∑ f ∈ (Finset.Icc 1 (m * n)).filter (fun f => f ∣ (m * n)), f.totient * ((m * n) / f) := by
    rw [hψ]
    positivity
  _ = ∑ f ∈ ((Finset.Icc 1 n).filter (fun d => d ∣ n) ×ˢ (Finset.Icc 1 m).filter (fun e => e ∣ m)), (f.1 * f.2).totient * ((m * n) / (f.1 * f.2)) := by
    rw [<-Finset.sum_attach ((Finset.Icc 1 (m * n)).filter (fun f => f ∣ (m * n))), <-Finset.sum_attach ((Finset.Icc 1 n).filter (fun d => d ∣ n) ×ˢ (Finset.Icc 1 m).filter (fun e => e ∣ m)), show ((Finset.Icc 1 n).filter (fun d => d ∣ n) ×ˢ (Finset.Icc 1 m).filter (fun e => e ∣ m)).attach = Finset.map ϕ Finset.univ by rw [Finset.map_univ_of_surjective ϕsurj, Finset.attach_eq_univ], Finset.sum_map Finset.univ ϕ]
    simp [ϕ]
    congr
    ext f
    obtain ⟨f, hf⟩ := f
    simp at hf ⊢
    have h₁ : f = Nat.gcd f n * Nat.gcd f m := by
      calc
        f = Nat.gcd f (m * n) := by symm; apply Nat.gcd_eq_left; exact hf.2
        _ = Nat.gcd f n * Nat.gcd f m := by rw [Nat.mul_comm]; apply Nat.Coprime.gcd_mul; rw [Nat.coprime_comm] at h; exact h
    rw [<-h₁]
  _ = ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d ∣ n), ∑ e ∈ (Finset.Icc 1 m).filter (fun e => e ∣ m), (d * e).totient * ((m * n) / (d * e)) := by rw [Finset.sum_product]
  _ = ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d ∣ n), ∑ e ∈ (Finset.Icc 1 m).filter (fun e => e ∣ m), d.totient * (n / d) * (e.totient * (m / e)) := by
    rw [Finset.sum_congr]
    rfl
    intro d hd
    rw [Finset.sum_congr]
    rfl
    intro e he
    simp at hd he
    rw [Nat.totient_mul]
    nth_rewrite 2 [Nat.mul_assoc]
    nth_rewrite 6 [Nat.mul_comm]
    nth_rewrite 2 [Nat.mul_assoc]
    rw [<-Nat.mul_assoc, Nat.div_mul_div_comm, Nat.mul_comm d e]
    exact he.2
    exact hd.2
    rw [Nat.Coprime, <-Nat.dvd_one, <-h]
    calc
      Nat.gcd d e ∣ Nat.gcd n e := by apply Nat.gcd_dvd_gcd_of_dvd_left; exact hd.2
      _ ∣ Nat.gcd m n := by rw [Nat.gcd_comm m n]; apply Nat.gcd_dvd_gcd_of_dvd_right; exact he.2
  _ = ∑ d ∈ (Finset.Icc 1 n).filter (fun d => d ∣ n), d.totient * (n / d) * ∑ e ∈ (Finset.Icc 1 m).filter (fun e => e ∣ m), (e.totient * (m / e)) := by
    congr
    ext d
    nth_rewrite 2 [Nat.mul_comm]
    rw [Finset.sum_mul]
    congr
    ext e
    ac_rfl
  _ = ψ m * ψ n := by
    rw [Nat.mul_comm, hψ, hψ, Finset.sum_mul]
    assumption'

/- (b) Prove that for each $a \in \mathbb{N}$ the equation $\psi(x)=a x$ has a solution. -/
theorem number_theory_25179_2 (a : ℕ) (apos : 0 < a) : ∃ x : ℕ, 0 < x ∧ ψ x = a * x := by
-- A solution is given by x = 2 ^ (2 * (a - 1)).
use 2 ^ (2 * (a - 1))
simp
-- Define embedding (injective function) s mapping numbers (ranging from 0 to 2 * (a - 1)) to divisors of 2 ^ (2 * (a - 1)).
let s : Finset.Icc 0 (2 * (a - 1)) ↪ (Finset.Icc 1 (2 ^ (2 * (a - 1)))).filter (fun d => d ∣ (2 ^ (2 * (a - 1)))) := ⟨fun k => ⟨2 ^ k.val, ?_⟩, ?_⟩
pick_goal 2
. -- Show that s is well-defined.
  obtain ⟨k, hk⟩ := k
  simp
  simp at hk
  refine ⟨⟨by apply Nat.one_le_pow; norm_num, by apply Nat.pow_le_pow_right; norm_num; exact hk⟩, by apply Nat.pow_dvd_pow; exact hk⟩
pick_goal 2
. -- Show that s is injective.
  simp [Function.Injective]
-- Show that s is surjective.
have ssurj : Function.Surjective s := by
  simp [Function.Surjective]
  intro d ⟨⟨hd₁, hd₂⟩, hd₃⟩
  rw [Nat.dvd_prime_pow] at hd₃
  obtain ⟨k, ⟨hd₃, hd₄⟩⟩ := hd₃
  use k
  use hd₃
  simp [s, hd₄]
  exact Nat.prime_two
calc
  ψ (2 ^ (2 * (a - 1))) = ∑ d ∈ (Finset.Icc 1 (2 ^ (2 * (a - 1)))).filter (fun d => d ∣ (2 ^ (2 * (a - 1)))), d.totient * ((2 ^ (2 * (a - 1))) / d) := by
    rw [hψ]
    simp
  _ = ∑ k : Finset.Icc 0 (2 * (a - 1)), (2 ^ k.val).totient * ((2 ^ (2 * (a - 1))) / 2 ^ k.val) := by
    simp
    rw [<-Finset.sum_attach ((Finset.Icc 1 (2 ^ (2 * (a - 1)))).filter (fun d => d ∣ (2 ^ (2 * (a - 1))))), show ((Finset.Icc 1 (2 ^ (2 * (a - 1)))).filter (fun d => d ∣ (2 ^ (2 * (a - 1))))).attach = Finset.map s Finset.univ by rw [Finset.map_univ_of_surjective ssurj, Finset.attach_eq_univ], Finset.sum_map Finset.univ s]
    simp [s]
  _ = ∑ k ∈ (Finset.Icc 0 (2 * (a - 1))).attach, (if k.val = 0 then (2 ^ k.val).totient * (2 ^ (2 * (a - 1)) / 2 ^ k.val) else 0) + ∑ k ∈ (Finset.Icc 0 (2 * (a - 1))).attach, (if k.val = 0 then 0 else (2 ^ k.val).totient * (2 ^ (2 * (a - 1)) / 2 ^ k.val)) := by
    rw [<-Finset.sum_add_sum_compl (Finset.univ.filter (fun k => k.val = 0)), Finset.compl_filter, Finset.sum_filter, Finset.sum_filter]
    simp
  _ = ∑ k ∈ (Finset.Icc 0 (2 * (a - 1))), (if k = 0 then (2 ^ k).totient * (2 ^ (2 * (a - 1)) / 2 ^ k) else 0) + ∑ k ∈ (Finset.Icc 0 (2 * (a - 1))), (if k = 0 then 0 else (2 ^ k).totient * (2 ^ (2 * (a - 1)) / 2 ^ k)) := by
    -- It seems that LEAN has some problem that rw [Finset.sum_attach] doesn't work, so we need rw [<-Finset.sum_attach].
    nth_rewrite 3 [<-Finset.sum_attach]
    nth_rewrite 4 [<-Finset.sum_attach]
    simp
  _ = 2 ^ (2 * (a - 1)) + ∑ k ∈ Finset.Icc 1 (2 * (a - 1)), (2 ^ k).totient * ((2 ^ (2 * (a - 1))) / 2 ^ k) := by
    simp
    rw [show Finset.Icc 0 (2 * (a - 1)) = Finset.Ico 0 1 ∪ (Finset.Ico 1 (2 * (a - 1) + 1)) by rw [Finset.Ico_union_Ico_eq_Ico]; congr; norm_num; omega, Finset.sum_union]
    simp [show Finset.Ico 1 (2 * (a - 1) + 1) = Finset.Icc 1 (2 * (a - 1)) by congr]
    rw [Finset.sum_congr]
    rfl
    intro k hk
    simp at hk
    simp [show ¬k = 0 by omega]
    simp
  _ = 2 ^ (2 * (a - 1)) + ∑ k ∈ Finset.Icc 1 (2 * (a - 1)), (2 ^ (2 * (a - 1))) / 2 := by
    simp [-Finset.sum_const]
    rw [Finset.sum_congr]
    rfl
    intro k hk
    simp at hk
    rw [Nat.totient_prime_pow (Nat.prime_two) (by omega)]
    simp
    have ha := le_trans hk.1 hk.2
    nth_rewrite 7 [show 2 = 2 ^ 1 by norm_num]
    rw [<-Nat.mul_div_assoc, <-Nat.pow_add, Nat.pow_div, Nat.pow_div ha]
    apply Nat.pow_right_injective
    norm_cast
    simp
    rw [<-Nat.sub_add_comm, Nat.add_sub_assoc, Nat.sub_add_comm]
    simp
    rfl
    exact ha
    exact hk.1
    norm_num
    rw [<-Nat.sub_add_comm, Nat.add_sub_assoc]
    simp
    exact ha
    exact hk.1
    norm_num
    apply Nat.pow_dvd_pow
    exact hk.2
  _ = a * 2 ^ (2 * (a - 1)) := by
    by_cases ha : a = 1
    . simp [ha]
    . simp
      rw [<-Nat.mul_div_assoc, show 2 * (a - 1) * (2 ^ (2 * (a - 1))) = (a - 1) * (2 ^ (2 * (a - 1))) * 2 by ac_rfl, Nat.mul_div_cancel]
      nth_rewrite 1 [<-Nat.one_mul (2 ^ (2 * (a - 1)))]
      rw [<-Nat.add_mul, Nat.add_comm, Nat.sub_add_cancel]
      omega
      norm_num
      apply dvd_pow_self
      omega

/- (c) Find all $a \in \mathbb{N}$ such that the equation $\psi(x)=a x$ has a unique solution. -/
theorem number_theory_25179_3 (a : ℕ) (apos : 0 < a) : (∃! x : ℕ, 0 < x ∧ ψ x = a * x) ↔ (∃ k : ℕ, a = 2 ^ k) := by
  -- Prove some lemmas similar to part (b).
  have h₂ (a : ℕ) : 2 * ψ (2 ^ a) = (a + 2) * 2 ^ a := by
    -- Define embedding (injective function) s mapping numbers (ranging from 0 to a) to divisors of 2 ^ a.
    let s : Finset.Icc 0 a ↪ (Finset.Icc 1 (2 ^ a)).filter (fun d => d ∣ (2 ^ a)) := ⟨fun k => ⟨2 ^ k.val, ?_⟩, ?_⟩
    pick_goal 2
    . -- Show that s is well-defined.
      obtain ⟨k, hk⟩ := k
      simp
      simp at hk
      refine ⟨⟨by apply Nat.one_le_pow; norm_num, by apply Nat.pow_le_pow_right; norm_num; exact hk⟩, by apply Nat.pow_dvd_pow; exact hk⟩
    pick_goal 2
    . -- Show that s is injective.
      simp [Function.Injective]
    -- Show that s is surjective.
    have ssurj : Function.Surjective s := by
      simp [Function.Surjective]
      intro d ⟨⟨hd₁, hd₂⟩, hd₃⟩
      rw [Nat.dvd_prime_pow] at hd₃
      obtain ⟨k, ⟨hd₃, hd₄⟩⟩ := hd₃
      use k
      use hd₃
      simp [s, hd₄]
      exact Nat.prime_two
    calc
      2 * ψ (2 ^ a) = 2 * ∑ d ∈ (Finset.Icc 1 (2 ^ a)).filter (fun d => d ∣ (2 ^ a)), d.totient * ((2 ^ a) / d) := by
        rw [hψ]
        simp
      _ = 2 * ∑ k : Finset.Icc 0 a, (2 ^ k.val).totient * ((2 ^ a) / 2 ^ k.val) := by
        simp
        rw [<-Finset.sum_attach ((Finset.Icc 1 (2 ^ a)).filter (fun d => d ∣ (2 ^ a))), show ((Finset.Icc 1 (2 ^ a)).filter (fun d => d ∣ (2 ^ a))).attach = Finset.map s Finset.univ by rw [Finset.map_univ_of_surjective ssurj, Finset.attach_eq_univ], Finset.sum_map Finset.univ s]
        simp [s]
      _ = 2 * ∑ k ∈ (Finset.Icc 0 a).attach, (if k.val = 0 then (2 ^ k.val).totient * (2 ^ a / 2 ^ k.val) else 0) + 2 * ∑ k ∈ (Finset.Icc 0 a).attach, (if k.val = 0 then 0 else (2 ^ k.val).totient * (2 ^ a / 2 ^ k.val)) := by
        rw [<-Finset.sum_add_sum_compl (Finset.univ.filter (fun k => k.val = 0)), Finset.compl_filter, Finset.sum_filter, Finset.sum_filter]
        rw [Nat.mul_add]
        simp
      _ = 2 * ∑ k ∈ (Finset.Icc 0 a), (if k = 0 then (2 ^ k).totient * (2 ^ a / 2 ^ k) else 0) + 2 * ∑ k ∈ (Finset.Icc 0 a), (if k = 0 then 0 else (2 ^ k).totient * (2 ^ a / 2 ^ k)) := by
        -- It seems that LEAN has some problem that rw [Finset.sum_attach] doesn't work, so we need rw [<-Finset.sum_attach].
        nth_rewrite 3 [<-Finset.sum_attach]
        nth_rewrite 4 [<-Finset.sum_attach]
        simp
      _ = 2 * 2 ^ a + 2 * ∑ k ∈ Finset.Icc 1 a, (2 ^ k).totient * ((2 ^ a) / 2 ^ k) := by
        simp
        rw [show Finset.Icc 0 a = Finset.Ico 0 1 ∪ (Finset.Ico 1 (a + 1)) by rw [Finset.Ico_union_Ico_eq_Ico]; congr; norm_num; omega, Finset.sum_union]
        simp [show Finset.Ico 1 (a + 1) = Finset.Icc 1 a by congr]
        rw [Finset.sum_congr]
        rfl
        intro k hk
        simp at hk
        simp [show ¬k = 0 by omega]
        simp
      _ = 2 * 2 ^ a + 2 * ∑ k ∈ Finset.Icc 1 a, (2 ^ a) / 2 := by
        simp [-Finset.sum_const]
        rw [Finset.sum_congr]
        rfl
        intro k hk
        simp at hk
        rw [Nat.totient_prime_pow (Nat.prime_two) (by omega)]
        simp
        have ha := le_trans hk.1 hk.2
        nth_rewrite 5 [show 2 = 2 ^ 1 by norm_num]
        rw [<-Nat.mul_div_assoc, <-Nat.pow_add, Nat.pow_div, Nat.pow_div ha]
        apply Nat.pow_right_injective
        norm_cast
        simp
        rw [<-Nat.sub_add_comm, Nat.add_sub_assoc, Nat.sub_add_comm]
        simp
        rfl
        exact ha
        exact hk.1
        norm_num
        rw [<-Nat.sub_add_comm, Nat.add_sub_assoc]
        simp
        exact ha
        exact hk.1
        norm_num
        apply Nat.pow_dvd_pow
        exact hk.2
      _ = (a + 2) * 2 ^ a := by
        by_cases ha : a = 0
        . simp [ha]
        . simp
          nth_rewrite 5 [show 2 = 2 ^ 1 by norm_num]
          rw [Nat.pow_div, <-Nat.mul_assoc, Nat.mul_comm 2 a, Nat.mul_assoc]
          nth_rewrite 3 [show 2 = 2 ^ 1 by norm_num]
          rw [<-Nat.pow_add, Nat.add_comm 1 (a - 1), Nat.sub_add_cancel, Nat.add_mul]
          ac_rfl
          omega
          omega
          norm_num
  have h₂' (a : ℕ) : 0 < a → ψ (2 ^ (2 * (a - 1))) = a * 2 ^ (2 * (a - 1)) := by
    intro apos
    specialize h₂ (2 * (a - 1))
    rw [show 2 * (a - 1) + 2 = 2 * a by nth_rewrite 2 [show a = a - 1 + 1 by rw [Nat.sub_add_cancel]; omega]; ring_nf, Nat.mul_assoc] at h₂
    simp at h₂
    exact h₂
  -- Break the iff into two implications.
  apply Iff.intro <;> intro h
  . -- If the solution is unique, then a = 2 ^ k for some k.
    obtain ⟨x, ⟨⟨_, h₂⟩, h₃⟩⟩ := h
    simp at h₃
    by_contra! h₄
    have h₅ := @Nat.exists_eq_two_pow_mul_odd a (show a ≠ 0 by omega)
    obtain ⟨k, m, ⟨h₅, h₆⟩⟩ := h₅
    have h₇ : m ≠ 1 := by
      by_contra! h₇
      simp [h₇] at h₆
      specialize h₄ k
      omega
    replace h₇ := @Nat.exists_prime_and_dvd m h₇
    obtain ⟨p, ⟨h₇, h₈⟩⟩ := h₇
    replace h₅ : Odd p := by
      by_contra!
      simp at this
      rw [Nat.Prime.even_iff] at this
      rw [this, <-even_iff_two_dvd] at h₈
      contrapose h₈
      simp
      assumption'
    replace h₈ : p ∣ a := by
      calc
        p ∣ m := h₈
        _ ∣ a := by rw [h₆]; apply Nat.dvd_mul_left
    rw [dvd_iff_exists_eq_mul_left] at h₈
    obtain ⟨c, h₈⟩ := h₈
    have h₈' := h₈
    replace h₈ : c = a / p := by
      rw [h₈, Nat.mul_div_cancel]
      apply Nat.Prime.pos h₇
    clear h₂
    have h₂'' : ψ (p ^ p * 2 ^ (2 * (c - 1))) = a * (p ^ p * 2 ^ (2 * (c - 1))) := by
      rw [number_theory_25179_1, h₂', <-Nat.mul_assoc, <-Nat.mul_assoc]
      simp [h₈']
      rw [Nat.mul_comm, Nat.mul_assoc]
      simp
      left
      -- Show that ψ (p ^ p) = p * p ^ p.
      -- Define embedding (injective function) s mapping numbers (ranging from 0 to p) to divisors of p ^ p.
      let s : Finset.Icc 0 p ↪ (Finset.Icc 1 (p ^ p)).filter (fun d => d ∣ p ^ p) := ⟨fun k => ⟨p ^ k.val, ?_⟩, ?_⟩
      pick_goal 2
      . -- Show that s is well-defined.
        obtain ⟨k, hk⟩ := k
        simp
        simp at hk
        refine ⟨⟨by apply Nat.one_le_pow; apply Nat.Prime.pos h₇, by apply Nat.pow_le_pow_right; norm_num; apply Nat.Prime.pos h₇; exact hk⟩, by apply Nat.pow_dvd_pow; exact hk⟩
      pick_goal 2
      . -- Show that s is injective.
        simp [Function.Injective]
        intro d₁ _ d₂ _ hd₁d₂
        apply Nat.pow_right_injective at hd₁d₂
        exact hd₁d₂
        apply Nat.Prime.two_le h₇
      -- Show that s is surjective.
      have ssurj : Function.Surjective s := by
        simp [Function.Surjective]
        intro d ⟨⟨hd₁, hd₂⟩, hd₃⟩
        rw [Nat.dvd_prime_pow] at hd₃
        obtain ⟨k, ⟨hd₃, hd₄⟩⟩ := hd₃
        use k
        use hd₃
        simp [s, hd₄]
        exact h₇
      calc
        ψ (p ^ p) = ∑ d ∈ (Finset.Icc 1 (p ^ p)).filter (fun d => d ∣ p ^ p), d.totient * (p ^ p / d) := by
          rw [hψ]
          apply Nat.pow_pos
          apply Nat.Prime.pos h₇
        _ = ∑ k : Finset.Icc 0 p, (p ^ k.val).totient * (p ^ p / p ^ k.val) := by
          simp
          rw [<-Finset.sum_attach ((Finset.Icc 1 (p ^ p)).filter (fun d => d ∣ p ^ p)), show ((Finset.Icc 1 (p ^ p)).filter (fun d => d ∣ (p ^ p))).attach = Finset.map s Finset.univ by rw [Finset.map_univ_of_surjective ssurj, Finset.attach_eq_univ], Finset.sum_map Finset.univ s]
          simp [s]
        _ = ∑ k ∈ (Finset.Icc 0 p).attach, (if k.val = 0 then (p ^ k.val).totient * (p ^ p / p ^ k.val) else 0) + ∑ k ∈ (Finset.Icc 0 p).attach, (if k.val = 0 then 0 else (p ^ k.val).totient * (p ^ p / p ^ k.val)) := by
          rw [<-Finset.sum_add_sum_compl (Finset.univ.filter (fun k => k.val = 0)), Finset.compl_filter, Finset.sum_filter, Finset.sum_filter]
          simp
        _ = ∑ k ∈ (Finset.Icc 0 p), (if k = 0 then (p ^ k).totient * (p ^ p / p ^ k) else 0) + ∑ k ∈ (Finset.Icc 0 p), (if k = 0 then 0 else (p ^ k).totient * (p ^ p / p ^ k)) := by
          -- It seems that LEAN has some problem that rw [Finset.sum_attach] doesn't work, so we need rw [<-Finset.sum_attach].
          nth_rewrite 3 [<-Finset.sum_attach]
          nth_rewrite 4 [<-Finset.sum_attach]
          simp
        _ = p ^ p + ∑ k ∈ Finset.Icc 1 p, (p ^ k).totient * (p ^ p / p ^ k) := by
          simp
          rw [show Finset.Icc 0 p = Finset.Ico 0 1 ∪ (Finset.Ico 1 (p + 1)) by rw [Finset.Ico_union_Ico_eq_Ico]; congr; norm_num; omega, Finset.sum_union]
          simp [show Finset.Ico 1 (p + 1) = Finset.Icc 1 p by congr]
          rw [Finset.sum_congr]
          rfl
          intro k hk
          simp at hk
          simp [show ¬k = 0 by omega]
          simp
        _ = p ^ p + ∑ k ∈ Finset.Icc 1 p, (p - 1) * p ^ (p - 1) := by
          simp [<-Finset.sum_const]
          rw [Finset.sum_congr]
          rfl
          intro k hk
          simp at hk
          rw [Nat.totient_prime_pow h₇ (by omega), Nat.mul_comm (p ^ (k - 1)) (p - 1), Nat.mul_assoc]
          simp
          left
          rw [Nat.pow_div, <-Nat.pow_add]
          congr
          rw [<-Nat.sub_add_comm, Nat.add_comm, Nat.sub_add_cancel]
          exact hk.2
          exact hk.1
          exact hk.2
          apply Nat.Prime.pos h₇
        _ = p * p ^ p := by
          simp
          ring_nf
          nth_rewrite 1 [show p = p ^ 1 by norm_num]
          rw [<-Nat.pow_add, Nat.add_comm 1 (p - 1), Nat.sub_add_cancel]
          nth_rewrite 2 [show p ^ p = p ^ p * 1 by norm_num]
          rw [<-Nat.mul_add, Nat.sub_add_cancel]
          ac_rfl
          all_goals
            exact le_trans (show 1 ≤ 2 by norm_num) (Nat.Prime.two_le h₇)
      by_contra!
      rw [h₈', show c = 0 by omega] at apos
      omega
      apply Nat.pow_pos
      apply Nat.Prime.pos h₇
      simp
      apply Nat.Coprime.pow_left
      apply Nat.Prime.coprime_pow_of_not_dvd
      exact Nat.prime_two
      exact Odd.not_two_dvd_nat h₅
    have h₃' := h₃
    -- We find two distinct solutions to the equation, hence arriving at a contradiction.
    specialize h₃ (2 ^ (2 * (a - 1)))
    simp [h₂' a apos] at h₃
    specialize h₃' (p ^ p * 2 ^ (2 * (c - 1)))
    simp [show 0 < p ^ p by apply Nat.pow_pos; apply Nat.Prime.pos h₇, h₂''] at h₃'
    replace h₃ : 2 ^ (2 * (a - 1)) = p ^ p * 2 ^ (2 * (c - 1)) := Eq.trans h₃ h₃'.symm
    clear h₂ h₂' h₃'
    replace h₃ : p ∣ 2 ^ (2 * (a - 1)) := by
      calc
        p ∣ p ^ p := by apply dvd_pow_self; linarith only [show 0 < p by apply Nat.Prime.pos h₇]
        _ ∣ 2 ^ (2 * (a - 1)) := by rw [h₃]; apply Nat.dvd_mul_right
    rw [Prime.dvd_pow_iff_dvd] at h₃
    apply Nat.le_of_dvd at h₃
    interval_cases p
    . tauto
    . tauto
    . tauto
    norm_num
    exact Nat.Prime.prime h₇
    by_contra! h₉
    replace h₉ : a = 2 ^ 0 := by
      omega
    specialize h₄ 0
    omega
  . -- If a = 2 ^ k, then the solution is unique.
    have h₁ := number_theory_25179_2 a apos
    obtain ⟨k, h₀⟩ := h
    obtain ⟨x, h₁⟩ := h₁
    -- Recall the definition of "exists and unique".
    simp [ExistsUnique]
    use x
    refine ⟨h₁, ?_⟩ -- The existence is already shown in part (b).
    have h₂ (y : ℕ) : 0 < y → ψ y = a * y → y = 2 ^ (2 * (a - 1)) := by
      intro ypos h₃
      have h₄ := @Nat.exists_eq_two_pow_mul_odd y (show y ≠ 0 by omega)
      obtain ⟨α, m, ⟨h₄, h₅⟩⟩ := h₄
      rw [h₀, h₅] at h₃
      -- We have ψ(m) > m for all m > 1.
      have h₈ : m > 1 → ψ m > m := by
        intro h₆
        dsimp [ψ]
        rw [gt_iff_lt, <-Nat.add_one_le_iff]
        calc
          m + 1 = ∑ k ∈ {1, m}, Nat.gcd k m := by rw [Finset.sum_pair, Nat.gcd_one_left, Nat.gcd_self, Nat.add_comm]; omega
          _ ≤ ∑ k ∈ Finset.Icc 1 m, Nat.gcd k m := by apply Finset.sum_le_sum_of_subset_of_nonneg; simp [Subset]; omega; intro k _ _; apply le_of_lt; apply Nat.gcd_pos_of_pos_right; omega
      have h₃' := h₃
      replace h₃ : 2 ^ (k + α + 1) * m = (α + 2) * (2 ^ α) * ψ m := by
        calc
          2 ^ (k + α + 1) * m = 2 * (2 ^ k * (2 ^ α * m)) := by rw [Nat.pow_add, Nat.pow_add]; norm_num; ac_rfl
          _ = 2 * ψ (2 ^ α * m) := by rw [h₃]
          _ = 2 * (ψ (2 ^ α) * ψ m) := by simp; apply number_theory_25179_1; simp; by_contra!; interval_cases m; tauto; apply Nat.Coprime.pow_left; apply Odd.coprime_two_left h₄
          _ = (2 * ψ (2 ^ α)) * ψ m := by ac_rfl
          _ = (α + 2) * (2 ^ α) * ψ m := by rw [h₂ α]
      -- We have ψ(m) odd if m odd.
      replace h₄ : Odd (ψ m) := by
        dsimp [ψ]
        rw [Finset.odd_sum_iff_odd_card_odd]
        suffices h₉ : (Finset.filter (fun x ↦ Odd (x.gcd m)) (Finset.Icc 1 m)).card = (Finset.Icc 1 m).card by
          rw [h₉, Nat.card_Icc]
          simp
          exact h₄
        congr
        ext x
        simp
        intro _ _
        by_contra! g₃
        simp at g₃
        rw [even_iff_two_dvd] at g₃
        replace g₃ : 2 ∣ m := by
          calc
            2 ∣ Nat.gcd x m := g₃
            _ ∣ m := by apply Nat.gcd_dvd_right
        rw [<-even_iff_two_dvd] at g₃
        absurd g₃
        simp
        exact h₄
      rw [show k + α + 1 = k + 1 + α by ac_rfl, Nat.pow_add, Nat.mul_comm, <-Nat.mul_assoc, Nat.mul_comm ((α + 2) * 2 ^ α) (ψ m), <-Nat.mul_assoc] at h₃
      simp at h₃
      replace h₃ : ψ m ∣ m * 2 ^ (k + 1) := by
        rw [h₃]
        apply dvd_mul_right
      apply Nat.Coprime.dvd_of_dvd_mul_right at h₃
      pick_goal 2
      . apply Nat.Coprime.pow_right
        apply Odd.coprime_two_right h₄
      have h₆ : m = 1 := by
        by_contra! h₆
        -- We get ψ(m) ≤ m, which is contradictory to our previous observation.
        apply Nat.le_of_dvd at h₃
        absurd h₃
        simp
        apply h₈
        all_goals
          by_contra!
          interval_cases m
          omega
          try tauto
      simp [h₆] at h₃ h₃' h₅
      clear h₄ h₆ h₈
      replace h₃ : 2 * ψ (2 ^ α) = 2 * (2 ^ k * 2 ^ α) := by
        rw [h₃']
      rw [h₂, <-Nat.mul_assoc, <-h₀] at h₃
      simp at h₃
      rw [Nat.mul_sub, <-h₃]
      norm_num
      exact h₅
    -- Any solution shall be equal to 2 ^ (2 * (a - 1)).
    intro y ypos h₃
    obtain ⟨h₁, h₁'⟩ := h₁
    have h₂' := h₂ y ypos h₃
    replace h₂ := h₂ x h₁ h₁'
    omega
