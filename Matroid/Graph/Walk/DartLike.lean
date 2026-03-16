import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

universe u'
open Set Graph

class HasDart (α : outParam Type*) (Gr : Type*) where
  verts (G : Gr) : Set α
  adj (G : Gr) : α → α → Prop
  dart : Gr → α → α → Sort*
  adj_iff_dart_like {G : Gr} {u v : α} : adj G u v ↔ Nonempty (dart G u v)
  left_mem_verts_of_adj {G : Gr} {u v : α} (h : adj G u v) : u ∈ verts G
  right_mem_verts_of_adj {G : Gr} {u v : α} (h : adj G u v) : v ∈ verts G

inductive HasDart.Walk {α : Type u'} {Gr : Type*} [HasDart α Gr] (G : Gr) : α → α → Type u'
  | nil {u v : α} (h : u = v) : Walk G u v
  | cons {u v w : α} {d : dart G u v} (p : Walk G v w) : Walk G u w

instance {α β : Type*} : HasDart α (Graph α β) where
  verts G := V(G)
  adj G := G.Adj
  left_mem_verts_of_adj {G : Graph α β} {u v : α} (h : G.Adj u v) := h.left_mem
  right_mem_verts_of_adj {G : Graph α β} {u v : α} (h : G.Adj u v) := h.right_mem
  dart G u v := {e : β | G.IsLink e u v}
  adj_iff_dart_like := nonempty_subtype.symm

instance {α : Type*} : HasDart α (SimpleGraph α) where
  verts _ := Set.univ
  adj G := G.Adj
  left_mem_verts_of_adj _ {u _ : α} _ := Set.mem_univ u
  right_mem_verts_of_adj _ {_ v : α} _ := Set.mem_univ v
  dart G u v := G.Adj u v
  adj_iff_dart_like := nonempty_prop.symm

variable {α β : Type u'} {u v : α} {e : β}

namespace HasDart

variable {Gr : Type*} [HasDart α Gr] (G : Gr) {u v w : α}

/- Manual instances for `DecidableEq` because deriving gives an instance that requires
  `DecidableEq Gr` -/
@[reducible]
instance Walk.instDecidable [DecidableEq α] [∀ u v, DecidableEq (dart G u v)] {u v}
    (p q : Walk G u v) : Decidable (p = q) := by
  rcases p with (nil | @⟨u, v₁, w, d₁, p₁⟩)
  <;> rcases q with (nil | @⟨u, v₂, w, d₂, p₂⟩)
  · exact isTrue rfl
  · exact isFalse (by simp)
  · exact isFalse (by simp)
  · by_cases hv : v₁ = v₂
    · subst hv
      simp only [cons.injEq, heq_eq_eq, true_and]
      haveI := Walk.instDecidable p₁ p₂
      infer_instance
    · apply isFalse (by simp [hv])

instance Walk.instDecidableEq [DecidableEq α] [∀ u v, DecidableEq (dart G u v)] {u v : α} :
    DecidableEq (Walk G u v) :=
  Walk.instDecidable G

end HasDart
