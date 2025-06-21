import Matroid.Graph.Tree

variable {α β : Type*} {G H T : Graph α β} {u v x y z : α} {e e' f g : β} {X : Set α} {F : Set β}
{P C W : WList α β} {n : ℕ}

open Set WList Function

namespace Graph

/-- A bipartion of `G` is a partition of the vertex set into two parts such that every edge
crosses the partition. -/
structure Bipartition (G : Graph α β) where
  left : Set α
  right : Set α
  union_eq : left ∪ right = V(G)
  disjoint : Disjoint left right
  forall_edge : ∀ e ∈ E(G), ∃ x ∈ left, ∃ y ∈ right, G.IsLink e x y

variable {B : G.Bipartition}

@[simps]
def Bipartition.symm (B : G.Bipartition) : G.Bipartition where
  left := B.right
  right := B.left
  union_eq := by rw [union_comm, B.union_eq]
  disjoint := B.disjoint.symm
  forall_edge e he := by
    obtain ⟨x, hx, y, hy, hxy⟩ := B.forall_edge e he
    exact ⟨y, hy, x, hx, hxy.symm⟩

lemma Bipartition.left_subset (B : G.Bipartition) : B.left ⊆ V(G) := by
  simp [← B.union_eq]

lemma Bipartition.right_subset (B : G.Bipartition) : B.right ⊆ V(G) := by
  simp [← B.union_eq]

lemma Bipartition.notMem_right {B : G.Bipartition} (hx : x ∈ B.left) : x ∉ B.right :=
  B.disjoint.notMem_of_mem_left hx

lemma Bipartition.notMem_left {B : G.Bipartition} (hx : x ∈ B.right) : x ∉ B.left :=
  B.disjoint.notMem_of_mem_right hx

lemma Bipartition.notMem_right_iff {B : G.Bipartition} (hxV : x ∈ V(G)) :
    x ∉ B.right ↔ x ∈ B.left := by
  refine ⟨fun h ↦ ?_, B.notMem_right⟩
  rwa [← B.union_eq, mem_union, or_iff_left h] at hxV

lemma Bipartition.notMem_left_iff {B : G.Bipartition} (hxV : x ∈ V(G)) :
    x ∉ B.left ↔ x ∈ B.right := by
  simpa using B.symm.notMem_right_iff hxV

/-- `B.Same x y` means that `x` and `y` are on the same side of `B`.
If `G` is connected, this is equivalent to `x` and `y` having even distance; see
 `Bipartiton.same_iff_dist_even`. -/
@[mk_iff]
protected structure Bipartition.Same (B : G.Bipartition) (x y : α) : Prop where
  left_mem : x ∈ V(G)
  right_mem : y ∈ V(G)
  mem_left_iff : x ∈ B.left ↔ y ∈ B.left

lemma Bipartition.Same.mem_right_iff {B : G.Bipartition} (h : B.Same x y) :
    x ∈ B.right ↔ y ∈ B.right := by
  rw [← B.notMem_left_iff h.left_mem, h.mem_left_iff, B.notMem_left_iff h.right_mem]

lemma Bipartition.Same.symm (h : B.Same x y) : B.Same y x where
  left_mem := h.right_mem
  right_mem := h.left_mem
  mem_left_iff := h.mem_left_iff.symm

lemma Bipartition.same_comm : B.Same x y ↔ B.Same y x :=
  ⟨.symm, .symm⟩

@[simp]
lemma Bipartition.same_self_iff : B.Same x x ↔ x ∈ V(G) := by
  simp [B.same_iff]

@[simp]
lemma Bipartition.symm_same : B.symm.Same = B.Same := by
  ext x y
  simp only [same_iff, symm_left, and_congr_right_iff]
  intro hx hy
  rw [← B.notMem_right_iff hx, ← B.notMem_right_iff hy, not_iff_not]

/-- `B.Opp x y` means that `x` and `y` are on opposite sides of `B`.
If `G` is connected, this is equivalent to `x` and `y` having odd distance; see
 `Bipartiton.opp_iff_dist_odd`. -/
@[mk_iff]
protected structure Bipartition.Opp (B : G.Bipartition) (x y : α) : Prop where
  left_mem : x ∈ V(G)
  right_mem : y ∈ V(G)
  mem_left_iff : x ∈ B.left ↔ y ∈ B.right

lemma Bipartition.Opp.symm (h : B.Opp x y) : B.Opp y x where
  left_mem := h.right_mem
  right_mem := h.left_mem
  mem_left_iff := by
    rw [← B.notMem_right_iff h.right_mem, ← h.mem_left_iff, B.notMem_left_iff h.left_mem]

lemma Bipartition.opp_comm : B.Opp x y ↔ B.Opp y x :=
  ⟨.symm, .symm⟩

lemma Bipartition.Opp.mem_right_iff (h : B.Opp x y) : x ∈ B.right ↔ y ∈ B.left :=
  h.symm.mem_left_iff.symm

lemma Bipartition.not_opp_iff {B : G.Bipartition} (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    ¬ B.Opp x y ↔ B.Same x y := by
  refine ⟨fun h ↦ ⟨hx, hy, ?_⟩, fun h h' ↦ ?_⟩
  · rwa [B.opp_iff, and_iff_right hx, and_iff_right hy, not_iff, not_iff_comm,
      B.notMem_right_iff hy, iff_comm] at h
  simp [B.same_iff, and_iff_right hx, and_iff_right hy, h'.mem_left_iff,
    ← B.notMem_left_iff hy] at h

lemma Bipartition.not_same_iff {B : G.Bipartition} (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    ¬ B.Same x y ↔ B.Opp x y := by
  rw [not_iff_comm, B.not_opp_iff hx hy]

lemma Bipartition.Same.not_opp (hB : B.Same x y) : ¬ B.Opp x y := by
  rwa [B.not_opp_iff hB.left_mem hB.right_mem]

lemma Bipartition.Opp.not_same (hB : B.Opp x y) : ¬ B.Same x y := by
  rwa [B.not_same_iff hB.left_mem hB.right_mem]

lemma Bipartition.opp_of_adj (B : G.Bipartition) (hxy : G.Adj x y) : B.Opp x y := by
  obtain ⟨e, h⟩ := hxy
  obtain ⟨x', hx', y', hy', h'⟩ := B.forall_edge e h.edge_mem
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.eq_and_eq_or_eq_and_eq h'
  · exact ⟨h.left_mem, h.right_mem, iff_of_true hx' hy'⟩
  refine ⟨h.left_mem, h.right_mem, iff_of_false ?_ ?_⟩
  · rwa [B.notMem_left_iff h.left_mem]
  rwa [B.notMem_right_iff h.right_mem]

@[simp]
lemma Bipartition.symm_opp : B.symm.Opp = B.Opp := by
  ext x y
  simp only [opp_iff, symm_left, symm_right, and_congr_right_iff]
  intro hx hy
  rw [← B.notMem_right_iff hx, ← B.notMem_right_iff hy]
  tauto

lemma Bipartition.Opp.trans (hxy : B.Opp x y) (hyz : B.Opp y z) : B.Same x z := by
  rw [B.same_iff, and_iff_right hxy.left_mem, and_iff_right hyz.right_mem, hxy.mem_left_iff,
    ← hyz.mem_right_iff]

lemma Bipartition.Same.trans (hxy : B.Same x y) (hyz : B.Same y z) : B.Same x z := by
  rw [B.same_iff, and_iff_right hxy.left_mem, and_iff_right hyz.right_mem, hxy.mem_left_iff,
    hyz.mem_left_iff]

@[simp]
lemma not_opp_self (B : G.Bipartition) (x : α) : ¬ B.Opp x x :=
  fun ⟨hx, _, h⟩ ↦ by simp [← B.notMem_left_iff hx] at h

def Bipartition.of_isSpanningSubgraph (B : H.Bipartition) (hHG : H ≤s G)
    (h_isLink : ∀ ⦃x y e⦄, e ∉ E(H) → G.IsLink e x y → B.Opp x y) : G.Bipartition where
  left := B.left
  right := B.right
  union_eq := by rw [← hHG.vertexSet_eq, B.union_eq]
  disjoint := B.disjoint
  forall_edge e he := by
    by_cases heH : e ∈ E(H)
    · obtain ⟨x, hx, y, hy, hexy⟩ := B.forall_edge e heH
      exact ⟨x, hx, y, hy, hexy.of_le hHG.le⟩
    obtain ⟨x, y, hexy⟩ := exists_isLink_of_mem_edgeSet he
    obtain hx | hx := B.union_eq ▸ hHG.vertexSet_eq ▸ hexy.left_mem
    · exact ⟨x, hx, y, by rwa [← (h_isLink heH hexy).mem_left_iff], hexy⟩
    exact ⟨y, by rwa [← (h_isLink heH hexy).mem_right_iff], x, hx, hexy.symm⟩

/-- A graph with a bipartition is bipartite. -/
def Bipartite (G : Graph α β) : Prop := Nonempty G.Bipartition

lemma Bipartition.bipartite (B : G.Bipartition) : G.Bipartite :=
  ⟨B⟩

/-- A subgraph of a bipartite graph is bipartite -/
lemma Bipartite.of_le (hG : G.Bipartite) (hle : H ≤ G) : H.Bipartite := by
  obtain ⟨B⟩ := hG
  refine ⟨⟨B.left ∩ V(H), B.right ∩ V(H), ?_, ?_, fun e he ↦ ?_⟩⟩
  · rw [← union_inter_distrib_right, B.union_eq,
      inter_eq_self_of_subset_right (vertexSet_mono hle)]
  · exact B.disjoint.mono inter_subset_left inter_subset_left
  obtain ⟨x, hx, y, hy, hxy⟩ := B.forall_edge e (edgeSet_mono hle he)
  replace hxy := hxy.of_le_of_mem hle he
  exact ⟨x, ⟨hx, hxy.left_mem⟩, y, ⟨hy, hxy.right_mem⟩, hxy⟩

/-- A disjoint union of bipartite graphs is bipartite. -/
lemma iUnion_disjoint_bipartite {ι : Type*} {H : ι → Graph α β}
    (hdj : Pairwise (Graph.Disjoint on H)) (hbp : ∀ i, Bipartite (H i)) :
    Bipartite <| Graph.iUnion H (hdj.mono fun _ _ h ↦ h.compatible) := by
  set B : ∀ i, (H i).Bipartition := fun i ↦ (hbp i).some
  refine ⟨⟨⋃ i, (B i).left, ⋃ i, (B i).right, ?_, ?_, ?_⟩⟩
  · simp +contextual [Bipartition.union_eq, ← iUnion_union_distrib]
  · simp only [disjoint_iUnion_right, disjoint_iUnion_left]
    intro i j
    obtain rfl | hne := eq_or_ne i j
    · exact (B i).disjoint
    exact (hdj hne.symm).vertex.mono (B j).left_subset (B i).right_subset
  simp_rw [iUnion_edgeSet, mem_iUnion, iUnion_isLink, forall_exists_index]
  intro e i he
  obtain ⟨x, hx, y, hy, hxy⟩ := (B i).forall_edge _ he
  exact ⟨x, ⟨i, hx⟩, y, ⟨i, hy⟩, ⟨i, hxy⟩⟩

lemma sUnion_disjoint_bipartite {s : Set (Graph α β)} (hdj : s.Pairwise Graph.Disjoint)
    (hbp : ∀ G ∈ s, G.Bipartite) : Bipartite <| (Graph.sUnion s (hdj.mono' (by simp))) := by
  apply iUnion_disjoint_bipartite
  · exact (pairwise_subtype_iff_pairwise_set s Graph.Disjoint).2 hdj
  simpa

lemma bipartite_iff_forall_component :
    G.Bipartite ↔ ∀ (H : Graph α β), H.IsComponent G → H.Bipartite := by
  refine ⟨fun h H hH ↦ h.of_le hH.le, fun h ↦ ?_⟩
  rw [G.eq_sUnion_components]
  exact sUnion_disjoint_bipartite G.pairwiseDisjoint_components <| by simpa

lemma Bipartition.same_first_get_iff (B : G.Bipartition) {W : WList α β} (hW : G.IsWalk W) {n : ℕ}
    (hn : n ≤ W.length) : B.Same W.first (W.get n) ↔ Even n := by
  induction n with
  | zero => simp [hW.first_mem]
  | succ n IH =>
  · have hopp : B.Opp (W.get (n+1)) (W.get n) := by
      obtain ⟨e, hinc⟩ := W.exists_dInc_get_get_succ (n := n) (by simpa using hn)
      exact B.opp_of_adj (hW.isLink_of_dInc hinc).adj.symm
    rw [Nat.even_add_one, ← IH (by omega)]
    refine ⟨fun h h' ↦ (h.symm.trans h').not_opp hopp, fun h ↦ ?_⟩
    rw [not_same_iff hW.first_mem hopp.right_mem] at h
    exact h.trans hopp.symm

lemma Bipartition.opp_first_get_iff (B : G.Bipartition) (hW : G.IsWalk W) (hn : n ≤ W.length) :
    B.Opp W.first (W.get n) ↔ Odd n := by
  rw [← B.not_same_iff hW.first_mem (hW.vertexSet_subset <| W.get_mem n),
    B.same_first_get_iff hW hn, Nat.not_even_iff_odd]

lemma Bipartition.same_iff_even_dist (B : G.Bipartition) (hG : G.Connected) (hx : x ∈ V(G))
    (hy : y ∈ V(G)) : B.Same x y ↔ Even (G.dist x y) := by
  obtain ⟨P, hP, rfl, rfl⟩ := (hG.vertexConnected hx hy).exists_isShortestPath
  simp [← hP.length_eq_dist, ← B.same_first_get_iff hP.isPath.isWalk le_rfl]

lemma Bipartition.opp_iff_odd_dist (B : G.Bipartition) (hG : G.Connected) (hx : x ∈ V(G))
    (hy : y ∈ V(G)) : B.Opp x y ↔ Odd (G.dist x y) := by
  rw [← Nat.not_even_iff_odd, ← B.same_iff_even_dist hG hx hy, B.not_same_iff hx hy]

/-- Every closed walk in a bipartite graph has an even number of edges. -/
lemma Bipartite.length_even_of_isWalk_isClosed (hG : G.Bipartite) (hC : G.IsWalk C)
    (h_closed : C.IsClosed) : Even C.length := by
  obtain ⟨B⟩ := hG
  cases C with
  | nil u => simp
  | cons u e W =>
  · simp only [cons_isClosed_iff, cons_isWalk_iff] at h_closed hC
    have h1 : B.Opp u W.first := by
      simpa [IsLink.walk] using B.opp_first_get_iff hC.1.walk_isWalk (n := 1) (by simp)
    have hlen := B.opp_first_get_iff hC.2 (n := W.length) le_rfl
    simp only [get_length, ← h_closed] at hlen
    rwa [cons_length, Nat.even_add_one, Nat.not_even_iff_odd, ← hlen, B.opp_comm]

/-- If there is vertex `r` such that adjacent vertices always have opposite-parity distance
to `r`, then `G` is bipartite. -/
lemma bipartite_of_forall_parity_adj_swap {r : α}
    (h : ∀ ⦃x y⦄, G.Adj x y → (Odd (G.dist r x) ↔ Even (G.dist r y))) : G.Bipartite := by
  refine ⟨⟨{x ∈ V(G) | Even (G.dist r x)}, {x ∈ V(G) | Odd (G.dist r x)}, ?_, ?_, ?_⟩⟩
  · exact subset_antisymm (by simp +contextual)
      fun _ _ ↦ by simpa [← and_or_left, Nat.even_or_odd]
  · simp +contextual [disjoint_left]
  rintro e he
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  obtain hrx | hrx := Nat.even_or_odd <| (G.dist r x)
  · exact ⟨x, ⟨hxy.left_mem, hrx⟩, y, ⟨hxy.right_mem, by rwa [h hxy.adj.symm]⟩, hxy⟩
  refine ⟨y, ⟨hxy.right_mem, by rwa [← h hxy.adj]⟩, x, ⟨hxy.left_mem, hrx⟩, hxy.symm⟩

lemma IsForest.bipartite {F : Graph α β} (hF : IsForest F) : F.Bipartite := by
  classical

  wlog hFt : F.IsTree with aux
  · exact bipartite_iff_forall_component.2 fun H hH ↦
      aux (hF.mono hH.le) ⟨hF.mono hH.le, hH.connected⟩
  have hlp := hF.loopless
  obtain ⟨r, hr⟩ := hFt.connected.nonempty
  apply bipartite_of_forall_parity_adj_swap (r := r)
  rintro x y ⟨e, hxy⟩
  rw [← Nat.odd_add]
  wlog hle : F.dist r x ≤ F.dist r y generalizing x y with aux
  · rw [add_comm]
    exact aux hxy.symm (not_le.1 hle).le
  obtain ⟨P, hP, hPfirst, hPlast⟩ :=
    (hFt.connected.vertexConnected hxy.left_mem hr).exists_isShortestPath
  have hPy : F.IsPath (WList.cons y e P)
  · suffices y ∉ P by simpa [cons_isPath_iff, hP.isPath, hPfirst, hxy.symm]
    intro hyP
    subst hPfirst hPlast
    have hle' := (hP.isPath.suffix <| P.suffixFromVertex_isSuffix y).isWalk.dist_le_length
    rw [suffixFromVertex_first hyP, suffixFromVertex_last, dist_comm] at hle'
    have hne : P.suffixFromVertex y ≠ P := by
      refine fun heq ↦ hxy.symm.adj.ne ?_
      rw [← heq, suffixFromVertex_first hyP]
    have hlt := (P.suffixFromVertex_isSuffix y).isSublist.length_lt hne
    rw [dist_comm] at hle
    linarith [hP.length_eq_dist]
  have hPl : P.length + 1 = F.dist y P.last := by simpa using
    (hF.isShortestPath_of_isPath hPy).length_eq_dist
  rw [← hPlast, ← hPfirst, dist_comm, ← hP.length_eq_dist, dist_comm, ← hPl]
  simp

/-- A graph is bipartite if and only if all its cycles are even -/
lemma bipartite_iff_forall_cycle_even : G.Bipartite ↔ ∀ C, G.IsCycle C → Even C.length := by
  refine ⟨fun h C hC ↦ h.length_even_of_isWalk_isClosed hC.isWalk hC.isClosed, fun h ↦ ?_⟩
  wlog hG : G.Connected with aux
  · exact bipartite_iff_forall_component.2 <|
      fun H hH ↦ aux (fun C hC ↦ h C (hC.of_le hH.le)) hH.connected
  obtain ⟨T, hT, hTG⟩ := hG.exists_isTree_spanningSubgraph
  obtain ⟨B⟩ := hT.isForest.bipartite
  refine ⟨B.of_isSpanningSubgraph hTG fun x y e he hexy ↦ ?_⟩
  have hxT : x ∈ V(T) := (hTG.vertexSet_eq ▸ hexy.left_mem)
  have hyT : y ∈ V(T) := (hTG.vertexSet_eq ▸ hexy.right_mem)
  rw [B.opp_iff_odd_dist hT.connected hxT hyT]
  obtain ⟨P, hP, rfl, rfl⟩ := (hT.connected.vertexConnected hxT hyT).exists_isShortestPath
  specialize h (cons P.last e P) ?_
  · exact (hP.isPath.of_le hTG.le).cons_isCycle hexy <| mt hP.isPath.isWalk.edge_mem_of_mem he
  rwa [cons_length, Nat.even_add_one, Nat.not_even_iff_odd, hP.length_eq_dist] at h
