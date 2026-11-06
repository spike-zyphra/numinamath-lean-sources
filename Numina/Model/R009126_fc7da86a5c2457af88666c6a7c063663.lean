import Mathlib

inductive Month | Jan | Feb | Mar | Apr | May | Jun | Jul | Aug | Sep | Oct | Nov | Dec

def Month.toFin : Month → Fin 12
  | .Jan => ⟨0, by simp⟩
  | .Feb => ⟨1, by simp⟩
  | .Mar => ⟨2, by simp⟩
  | .Apr => ⟨3, by simp⟩
  | .May => ⟨4, by simp⟩
  | .Jun => ⟨5, by simp⟩
  | .Jul => ⟨6, by simp⟩
  | .Aug => ⟨7, by simp⟩
  | .Sep => ⟨8, by simp⟩
  | .Oct => ⟨9, by simp⟩
  | .Nov => ⟨10, by simp⟩
  | .Dec => ⟨11, by simp⟩

def Fin.toMonth : Fin 12 → Month
  | ⟨0, _⟩ => .Jan
  | ⟨1, _⟩ => .Feb
  | ⟨2, _⟩ => .Mar
  | ⟨3, _⟩ => .Apr
  | ⟨4, _⟩ => .May
  | ⟨5, _⟩ => .Jun
  | ⟨6, _⟩ => .Jul
  | ⟨7, _⟩ => .Aug
  | ⟨8, _⟩ => .Sep
  | ⟨9, _⟩ => .Oct
  | ⟨10, _⟩ => .Nov
  | ⟨11, _⟩ => .Dec

theorem number_theory_15927 (first : Month) (hf : first = .May) (n : ℕ) (hn : n = 25) :
    (first.toFin + (n - 1) * 5).toMonth = .May := by
  subst hn
  subst hf
  simp [Month.toFin, Fin.toMonth]
  <;> try { native_decide }
  all_goals norm_num
  <;> try { aesop }
  <;> try { native_decide }