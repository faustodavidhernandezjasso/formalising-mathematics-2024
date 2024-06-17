/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro h1
  rw [h1]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro hPQ
  rw [hPQ]
  intro hQP
  rw [hQP]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hPQ
  intro hQR
  rw [hPQ]
  rw [hQR]
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro h1
  cases' h1 with hP hQ
  constructor
  exact hQ
  exact hP
  intros h2
  constructor
  cases' h2 with hQ1 hP1
  exact hP1
  cases' h2 with hQ1 hP1
  exact hQ1
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro h1
  constructor
  cases' h1 with hPQ hR
  cases' hPQ with hP hQ
  exact hP
  constructor
  cases' h1 with hPQ hR
  cases' hPQ with hP hQ
  exact hQ
  cases' h1 with hPQ hR
  cases' hPQ with hP hQ
  exact hR
  intro h1
  constructor
  constructor
  cases' h1 with hP hQR
  exact hP
  cases' h1 with hP hQR
  cases' hQR with hQ hR
  exact hQ
  cases' h1 with hP hQR
  cases' hQR with hQ hR
  exact hR
  done

example : P ↔ P ∧ True := by
  constructor
  intros hP
  constructor
  exact hP
  triv
  intros h1
  cases' h1 with hP hT
  exact hP
  done

example : False ↔ P ∧ False := by
  constructor
  intro hF
  constructor
  exfalso
  exact hF
  exact hF
  intro h1
  cases' h1 with hP hF
  exact hF
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro h1
  intro h2
  rw [h1, h2]
  done

example : ¬(P ↔ ¬P) := by
  change (P ↔ ¬P) → False
  intro h1
  cases' h1 with h2 h3
  by_contra h4
  change False → False at h4
  by_cases hP : P
  apply h2 at hP
  change P → False at hP
  apply hP
  apply h3
  change P → False
  intro hP0
  apply hP
  exact hP0
  change P → False at hP
  apply hP
  apply h3
  change P → False
  exact hP
  done
