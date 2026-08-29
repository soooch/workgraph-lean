# Work Graph Model — Quasi-Formal Specification

Sections 1–4 are definitions and axioms only. Everything derivable is in §5;
exclusions, deferrals, and rejected alternatives in §6. Convention: β and θ
are formation-time data (2.4), not fields of terms; `Leaf(N)` and
`Series(W₁, W₂)` leave them implicit where irrelevant.

## 1. Syntax

**1.1 (Work terms).** Work terms are elaborated objects:

```
W ::= Leaf(N, bind) | Series(W₁, W₂) | Par(W₁, W₂)
```

where N ranges over primitive nodes and `bind : InSlots(N) → 𝔸` is the
leaf's current binding (2.2). Terms are constructed only by the formations
of 2.4, which take β (leaf instantiation) and θ (Series) as arguments and do
not retain them. Each leaf is a distinct node instance of its primitive N,
created fresh at instantiation (2.4): two instantiations of the same N are
different leaves, and `res`, `producer`, and ≺ (4.3) range over instances,
never over primitive symbols. The term tree is called the SP tree.
(Intuition, non-normative: a work term corresponds to a two-terminal
series-parallel DAG, Series composing end-to-end and Par side-by-side.)

**1.2 (Primitive node).** A primitive node N declares:

- finite, possibly empty, named sets of input slots and output slots;
- a provenance declaration `prov_N : OutSlots(N) → InSlots(N) ⊎ {★}`;
- for each input slot and each **fresh** output slot (those with
  `prov_N(outₖ) = ★`), a fixed `len ∈ ℕ` and `align ∈ ℕ` (power of two).

`prov_N(outₖ) = ★` mints a fresh allocation (a **fresh** slot);
`prov_N(outₖ) = inⱼ` re-exposes, untouched, whatever allocation is bound to
inⱼ (a **passthrough** slot). Passthrough slots carry only their `prov`
pointer — no declarations of their own.

## 2. Allocations and Provenance

**2.1 (Allocation IDs).** Let `𝔸 = 𝔸_★ ⊎ 𝔸_π`:

- `𝔸_★` (*produced*): each fresh output slot of each node instance introduces
  a distinct `a ∈ 𝔸_★`. Its *true producer* is the node owning that slot; it
  carries the slot's declared `len`.
- `𝔸_π` (*parameters*): nominal identifiers, each declared with a fixed
  `(len, align)`, standing for buffers produced outside the term. A parameter
  has no producer within any work term — work terms are open terms and their
  parameters are their free variables. Distinct input slots bound to the same
  parameter share that external buffer by name.

**2.2 (Resolution).** Each leaf carries its total binding `bind` (1.1).
Define `res(node, slot) ∈ 𝔸`:

```
res(N, inⱼ)  = bind(N, inⱼ)
res(N, outₖ) = fresh id of (N, outₖ)      if prov_N(outₖ) = ★
res(N, outₖ) = bind(N, prov_N(outₖ))      otherwise
```

**2.3 (ID-set functions).** For a work term, define `inputs`, `outputs`,
`buffers : W → 𝒫(𝔸)` (all provenance-resolved; always read against the
term's current bindings — see 2.4):

```
inputs(Leaf(N))        = { res(N, inⱼ) | inⱼ ∈ InSlots(N) }
inputs(Series(W₁, W₂)) = inputs(W₁)
inputs(Par(W₁, W₂))    = inputs(W₁) ∪ inputs(W₂)

outputs(Leaf(N))        = { res(N, outₖ) | outₖ ∈ OutSlots(N) }
outputs(Series(W₁, W₂)) = outputs(W₂)
outputs(Par(W₁, W₂))    = outputs(W₁) ∪ outputs(W₂)

buffers(Leaf(N))        = inputs(Leaf(N)) ∪ outputs(Leaf(N))
buffers(Series(W₁, W₂)) = buffers(W₁) ∪ buffers(W₂)
buffers(Par(W₁, W₂))    = buffers(W₁) ∪ buffers(W₂)

internal(W) = buffers(W) − inputs(W) − outputs(W)
```

**2.4 (Formation).** Terms are built only by these three operations; a term
so built is *structurally well-formed*:

- **Instantiate**: given N and `β : InSlots(N) → 𝔸_π`, form `Leaf(N, β)` — a
  leaf whose binding is β, carrying a fresh node-instance identity (1.1) and
  minting fresh IDs at its ★ slots (2.1).
- **Series**: given structurally well-formed W₁, W₂ and a substitution θ with
  `dom(θ) = inputs(W₂)` exactly and `range(θ) ⊆ outputs(W₁)` (surjectivity
  not required), both judged against W₂'s bindings as they stand at
  formation, form `Series(W₁, W₂′)` where W₂′ is W₂ with every leaf binding
  rewritten by

  ```
  bind′(s) = θ(bind(s))   if bind(s) ∈ dom(θ)
  bind′(s) = bind(s)      otherwise
  ```

  evaluated against pre-formation bindings — simultaneous, applied once,
  never iterated. W₁'s bindings are untouched. θ is consumed at formation and
  not retained (a retained θ's type would go stale under enclosing rewrites).
  The composite contains the *rewritten* W₂.
- **Par**: form `Par(W₁, W₂)` from structurally well-formed W₁, W₂; no
  bindings are introduced or changed. Branches share interface inputs by
  naming the same parameter.

Formation operands are *closed*: structural well-formedness is a property of
whole terms as formed, and by D3 a closed term's inputs are parameters.
Operands never share node instances — a term is consumed by the formation
that uses it, and reusing one requires re-instantiation. A subterm of a
closed term is merely *scoped*: enclosing formations may have rewritten its
bindings to produced IDs, and scoped subterms are not formation operands —
the rewritten arm W₂′ exists only inside its composite. Hence every θ is
judged against a closed arm, so `dom(θ) = inputs(W₂) ⊆ 𝔸_π` (D3/D4): a
produced-valued binding is never in any θ's domain.

## 3. Data Semantics

**3.1 (Read-only inputs).** No node writes any allocation it did not freshly
produce.

**3.2 (Extensionality).** A node's behavior is a function of its fixed
declaration (1.2) and, per input slot, the bytes bound to it — and of
nothing else.

**3.3 (Validity).** A work term is *length-valid* iff, per input slot, after
resolution: the slot's declared `len` equals `len(res(N, inⱼ))`. Per-slot
checks; no constraint solving. `W_wf` denotes the terms that are both
structurally well-formed (2.4) and length-valid.

## 4. Finalization

**4.1 (Type boundary).** `finalize : W_wf → G`, defined only on well-formed
terms. A finalized graph G is **not** a work term and cannot be composed.
All scheduling and allocation decisions occur exactly once, at finalization,
over the full SP tree.

**4.2 (Sentinels).** Define `inputs(G) := inputs(W)` and
`outputs(G) := outputs(W)`. Extend the node instances of W with two sentinel
*events* σ and τ, carrying no slots and no declarations:

- `producer(p) := σ` for every parameter p occurring in W (contents
  caller-provided before execution; σ performs no computation);
- τ marks completion and is a user of every `a ∈ inputs(W) ∪ outputs(W)`
  (4.4).

The sentinels encode the interface-accessibility requirement (inputs stable
for the entire run — a deliberate memory cost); the property they enforce is
stated and derived in D12.

**4.3 (Schedule and order).** A schedule S assigns each Par node in W a mode:

```
mode(Par(W₁, W₂)) ∈ { concurrent, seq(1,2), seq(2,1) }
```

Let ≺ be the transitive closure of the union of the following generator sets
(σ, τ the sentinel events of 4.2):

- { (σ, n), (n, τ) } for every node instance n of W;
- `Series(W₁, W₂)`: { (n₁, n₂) } for every n₁ ∈ W₁, n₂ ∈ W₂;
- `Par` with `seq(i,j)`: { (nᵢ, nⱼ) } for every nᵢ ∈ Wᵢ, nⱼ ∈ Wⱼ;
- `Par` concurrent: none.

Execution contract: every memory access a node instance performs — reads of
its inputs' allocations, writes of its fresh outputs — occurs within that
instance's start–finish span, and an instance may start only after every
≺-predecessor has finished. ≺ is the only ordering primitive; no notion of
time is defined beyond the spans it constrains.

**4.4 (Conflict).** For allocation a, let

```
users(a) = { producer(a) }
         ∪ { n | n has an input slot resolving to a }
         ∪ { τ | a ∈ inputs(W) ∪ outputs(W) }
```

with `producer(p) = σ` for parameters (4.2) and the minting instance for
produced IDs (2.1). Define:

```
mayOverlap(a, b) ⟺ ¬(∀u ∈ users(a). u ≺ producer(b))
                 ∧ ¬(∀u ∈ users(b). u ≺ producer(a))
```

i.e., a and b conflict unless one is fully finished — producer and all
consumers — before the other's producer starts.

**4.5 (Arena and packing).** One backing arena. The *effective alignment* of
an allocation is `align(a) = max` of: the declared align of every slot
resolving to a (input and fresh slots; passthrough slots carry none), and,
when a is a parameter, a's own declared align (σ carries no slots, so the
parameter's declaration enters directly). An *assignment* maps each
`a ∈ buffers(W)` to `offset(a) ∈ ℕ` such that:

```
offset(a) ≡ 0 (mod align(a))

a ≠ b ∧ mayOverlap(a, b)
    ⟹ [offset(a), offset(a)+len(a)) ∩ [offset(b), offset(b)+len(b)) = ∅
```

Arena size = `max({0} ∪ { offset(a) + len(a) })`; arena alignment =
`max({1} ∪ { align(a) })` (an allocation-free term gets a size-0,
alignment-1 arena). A *feasible finalization* is a pair (S, assignment).
`finalize` returns one; the selection policy — the objective (arena size vs.
a latency/memory trade-off) and tie-breaking among feasible finalizations —
is deliberately open (§6).

**4.6 (Emitted artifact).** `finalize` returns:

- arena `(size, alignment)`;
- dispatch structure — linear order where sequentialized, dependency sets
  where concurrent — in which every dispatch carries, per slot of its node,
  the resolved arena offset of that slot's allocation (operands are lowered
  to base-relative offsets at emission);
- offset table restricted to interface allocations: the ABI projection of
  the assignment.

Runtime performs no memory logic: buffer address = base + offset.

**4.7 (ABI).** Caller allocates the arena, writes `inputs(G)` at their
offsets, executes, reads `outputs(G)` at their offsets.

## 5. Derived Properties and Remarks

**D1 (Output categories are exhaustive and unrestricted).** By the type of
`prov_N` (1.2): fresh and passthrough are the only cases; forwarding is
whole-buffer because the codomain is slots, not slices; whether a kernel also
reads a forwarded input is unmodeled and irrelevant; neither `prov_N` nor β
need be injective — several slots naming one allocation resolve to the same
ID, inert by D11.

**D2 (Resolution is a lookup).** In the elaborated model, `res` (2.2) is
non-recursive: one `bind` lookup, plus one intra-node `prov` hop for
outputs. Under an eager, fully materialized representation of bindings,
Series formation rewrites each binding at most once per enclosing Series —
O(nesting depth) per slot — and lookup is O(1); lazier representations trade
lookup cost against formation cost. The semantics (2.4) fixes only values,
not representation.

**D3 (Composition closure).** By induction over the formations of 2.4:
`bind` is total at every stage, so `res` is; `inputs(W₂′) ⊆ outputs(W₁)` in
`Series(W₁, W₂′)` holds by construction; and the inputs of any closed term
(2.4) are exactly its free parameters: `inputs(W) ⊆ 𝔸_π` — indeed every
parameter-valued binding anywhere in W names a member of `inputs(W)`, so the
parameters occurring in W are exactly `inputs(W)`. Series rewrites every
such binding of W₂ through θ, possibly to a *forwarded parameter* of W₁;
parameter bindings may thus survive formation, but only as free variables of
the composite, since a parameter in `outputs(W₁)` lies in `inputs(W₁)`
(induction: a leaf exposes a parameter only by passthrough of a slot bound
to it; Series and Par preserve the containment). Composition is capture-free
substitution on open terms — parameters behave precisely as free variables.
Consequently finalization closes the term: σ's producer assignment (4.2)
covers every parameter occurring in W — exactly `inputs(W)` — and with 2.1,
every allocation occurring in G has exactly one producer.

**D4 (Externality).** At every Series formation, `dom(θ) ⊆ 𝔸_π`: the right
arm is closed at formation (2.4), so `dom(θ)` is its inputs, ⊆ 𝔸_π by D3.
Hence a binding, once produced-valued, is never rewritten. Consequently, for
any subterm V of any work term: every ID in `buffers(V)` not minted by a node
of V lies in `inputs(V)`. Induction: when V is formed it is closed, and its
non-local IDs are exactly its parameters, which D3 places at its input
boundary; each enclosing substitution rewrites by ID value, so a boundary
occurrence and an interior occurrence of one ID map to the same image —
whether that image is a parameter or an ID minted in the enclosing left arm —
preserving the containment through every rewrite.

**D5 (Unfolded internals).** From 2.3, D3, and D4 (both inclusions of the
Series equality use D4, e.g. `internal(W₁) ∩ outputs(W₂) = ∅`: such an a
would be non-local in `buffers(W₂)`, hence in `inputs(W₂) ⊆ outputs(W₁)`,
contradicting internality):

```
internal(Series(W₁, W₂)) = internal(W₁) ∪ internal(W₂)
                         ∪ (outputs(W₁) − inputs(W₁) − outputs(W₂))
internal(Par(W₁, W₂))    = internal(W₁) ∪ internal(W₂)
```

**D6 (Locality of deadness).** `a ∈ internal(W)` ⟹ `users(a) ⊆ nodes(W)`.
Inward: producer(a) ∈ W, since by D4 a non-locally-minted or parameter ID in
`buffers(W)` would lie in `inputs(W)`, contradicting internality. Outward:
absence from `outputs(W)` leaves no forwarding path out, and sharing by
parameter name is excluded since a ∉ 𝔸_π. Conversely, interface members are
exposed: nothing in W's structure certifies a member of
`inputs(W) ∪ outputs(W)` dead, and since 1.2 places no closure on declarable
signatures, an enclosing context witnessing an outside user is always
constructible — a Par sibling naming the same parameter for `a ∈ inputs(W)`,
a downstream Series consumer of matching `len` for `a ∈ outputs(W)`.
(Relative to a fixed, poorer primitive universe, only the syntactic reading
holds.) So `internal(W)` is exactly the set W's structure alone proves dead.

**D7 (No in-place — unrepresentable).** No allocation has more than one
writer — its true producer: 3.1 forbids writes to non-fresh allocations, and
`prov_N` makes every output either ★-fresh or an untouched re-exposure.
"Same allocation, new contents" has no syntax.

**D8 (≺ is a strict partial order).** Every generator pair of 4.3 respects
the left-to-right linearization of the SP tree taken with mode order (seq(2,1)
reversing its branches), with σ prepended and τ appended: Series and seq pairs
relate disjoint node sets in linearization order, and σ/τ pairs are endpoint
pairs. The generators embed in a total order, hence so does their transitive
closure, which is therefore irreflexive.

**D9 (Dataflow respects ≺).** For every allocation a and every
c ∈ users(a) ∖ {producer(a)}: `producer(a) ≺ c`. Induction over the
formations, using D4's observation that produced-valued bindings are final:
a slot's value is either its leaf parameter — whose producer after
finalization is σ, and σ ≺ c — or was set produced-valued by exactly one
Series formation, whose range lies in the left arm's outputs while c sits in
the right arm, so the Series clause gives producer ≺ c; passthrough creates
no new consumers. Case c = τ: producer(a) ≺ τ by the (n, τ) generators when
producer(a) ∈ W, and σ ≺ τ through any node of W (nonempty by 1.1) when
producer(a) = σ. This lemma is also what makes the execution contract (4.3)
correct: for produced allocations, access containment puts the producer's
write span inside its start–finish span, which every consumer's span
follows; for parameters, caller initialization precedes execution entirely
(4.7) — σ performs no write — and σ ≺ c places every consumer after that
boundary.

**D10 (Node-local disjointness).** Let b be a fresh output of N and a resolve
to an input slot of N. First conjunct of `mayOverlap(a, b)`: N ∈ users(a),
producer(b) = N, and ≺ is strict (D8), so N ⊀ N. Second conjunct: N ∈
users(b), and N ≺ producer(a) is impossible since producer(a) ≺ N (D9) and ≺
is irreflexive. Hence `mayOverlap(a, b)` and 4.5 forces address disjointness —
a node's fresh output can never occupy an input's space. Corollary (positive
lengths): every node's input and fresh-output byte ranges are disjoint;
hence in a chain, consecutive interior allocations conflict, so at least two
interior buffers are simultaneously placed — the ping-pong lower bound.
(Sufficiency of exactly two interior buffers is a separate claim, needing
equal lengths and compatible alignments, and sits on top of the pinned
interface allocations D12 adds.)

**D11 (Provenance opacity).** By 3.2, from a node's perspective an input is
bytes of declared `(len, align)` — behavior cannot depend on addresses or on
whether slots alias, since neither is among the function's arguments.
Unobservable in particular are: whether two input slots resolve to the same
allocation (immutability, 3.1, makes aliased slots bit-identical
throughout); whether an input's provenance is a parameter or an upstream
produced ID; and whether it arrived directly or through passthrough chains.
(The syntactic fact that node declarations never mention 𝔸 makes 3.2
satisfiable by ordinary kernels; 3.2 itself is what delivers
unobservability.) Corollary (substitution): rebinding preserves the
interior's input–output function — for any byte environment, evaluating the
rewritten W₂ with each rebound slot reading θ(p)'s bytes equals evaluating
standalone W₂ with p bound to those same bytes. (Outputs differ when the
supplied bytes differ; what is invariant is the function, not its value.)
This is what makes Series formation sound without inspecting W₂ —
finalization (4.2) touches no bindings at all. Lowering-level exceptions
(descriptor-binding limits etc.) are per-target legality checks, remedied by
explicit copy nodes.

**D12 (Interface pinning).** For every interface allocation a, τ ∈ users(a)
(4.4), and nothing satisfies τ ≺ n (4.3, D8). So for interface a and any b:
`∀u ∈ users(a). u ≺ producer(b)` fails at u = τ, hence `mayOverlap(a, b)`
reduces to `¬(∀u ∈ users(b). u ≺ producer(a))`. Consequences: two interface
allocations always conflict (each has τ among users), hence are pairwise
address-disjoint — except identical IDs from passthrough of an input of W to
an output of W, the one sanctioned coincidence; an input of W (producer σ,
nothing ≺ σ) conflicts with every other allocation — fully pinned; an
interface output may still reuse the space of an allocation wholly finished
before its producer starts, and conversely nothing may be placed over it from
its producer onward (τ ∈ users forbids the required ordering). With access
containment (4.3), these consequences constitute the guarantee the sentinels
of 4.2 encode: interface allocations are pairwise address-disjoint, each
exclusively and stably placed from its producer's start to the end of
execution — inputs pinned for the whole run, all interface allocations
concurrently accessible at completion — regardless of S.

**D13 (Series order exceeds data dependency — deliberately).** θ need not be
surjective (2.4), so W₁ may contain dead-end nodes with no data path into W₂
(e.g. `Series(Par(Leaf(A), Leaf(C)), Leaf(B), θ)` with θ binding only A's
output). The Series clause of 4.3 orders such nodes before W₂ anyway — a
strict superset of the order D9 accounts for. This is load-bearing: D14's
guarantee that all of `internal(W₁)` is reusable in W₂ requires every user in
W₁ — dead ends included — to precede W₂.

**D14 (Reuse legality).** Unfolding 4.4/4.5: a ≠ b may share addresses iff
`¬mayOverlap(a, b)`, i.e. one is wholly finished before the other's producer
starts — which access containment (4.3) makes semantically sufficient, not
merely model-internal. Consequences: concurrent Par branches admit no
cross-branch reuse (no order exists between them); shared read-only inputs
are counted once, and consumers of a shared allocation need no mutual
ordering (reads commute by 3.1 + 3.2); for `Series(W₁, W₂)`, every
`a ∈ internal(W₁)` has `users(a) ⊆ nodes(W₁)` (D6) all ≺ every node of W₂
(4.3), so all of `internal(W₁)` is reusable by every fresh allocation in W₂;
and for `Par` with mode `seq(i,j)`, likewise every `a ∈ internal(Wᵢ)` — the
earlier branch — is reusable by every fresh allocation in Wⱼ.

**D15 (Packing is DSA).** Minimizing arena size under 4.5 is dynamic storage
allocation on the conflict graph — NP-hard, and the hardness is realizable
within the model: any DSA instance `{(sᵢ, eᵢ, lenᵢ)}` with WLOG sᵢ < eᵢ
(subdivide ticks; hardness is preserved) is realized by a pure Series chain
of tick nodes (empty slot sets permitted by 1.2, so source and terminal ticks
need no dummies) where tick sᵢ mints allocation i fresh, ticks strictly
between sᵢ and eᵢ forward it by passthrough, and tick eᵢ consumes without
forwarding. Lower bound: max weight of a clique in the conflict graph; the
gap to it is fragmentation. S and the assignment are coupled through
`mayOverlap`; practical decomposition: choose S to minimize the clique bound,
then pack (first-fit over a linearization as baseline).

## 6. Deliberately Excluded / Deferred / Rejected

- **In-place aliasing** — unrepresentable (D7). Minimal reintroduction path,
  if ever wanted: model-invisible allocator relaxation via per-node
  `overlap_safe(outₖ, inⱼ)` declarations plus a last-alias predicate checked
  against the schedule.
- **Slice passthrough** — excluded; valid extension by enriching the codomain
  of `prov_N` to `(inⱼ, offset, len)` under provenance tracking.
- **Multiple arenas / memory spaces** — deferred; the packing interface should
  carry an arena ID per allocation so this remains a parameter, not a
  redesign.
- **Caller-provided placement** — compatible future extension to 4.7: such
  slots become externally-satisfied intervals excluded from packing.
- **Partial θ** (Series inputs bypassing W₁, merged by parameter name) —
  rejected: totality of θ encodes the SP routing discipline that all data
  enters a series composite through its first stage; the identity-plumbing
  cost of routing a parameter past W₁ is the accepted, memory-harmless price.
- **Selection policy** — open: the objective over feasible finalizations
  (pure arena-size minimization vs. a latency/memory Pareto) and tie-breaking
  among optima; the only remaining free choice before the finalization
  algorithm.
