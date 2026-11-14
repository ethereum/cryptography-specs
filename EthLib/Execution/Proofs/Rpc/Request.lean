module

public import EthLib.Execution.Rpc.Request
public import EthLib.Serialization.Proofs.JsonRpc
-- The members of an encoded object unfold the JSON object builder of Lean.
import all Lean.Data.Json.Basic

/-!
# Proofs: requests and responses

The readers of requests and responses read back what their writers write.

A request reads back with its parameters, whether it has any or not.

A JSON value reads as a request exactly when it is an object of this form.

Its only members are `jsonrpc`, `id`, `method` and `params`, and `params` may be missing.

Its version is `2.0`, its identifier a string, a number or `null`, and its method a string.

Its parameters, when present, are an array.

A response reads back with its result, even `null`, or with its error object.

A JSON value reads as a response exactly when it is an object of three members.

They are the version `2.0`, the identifier, and either the result or an error object.
-/

public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Serialization.JsonRpc

/-- An identifier is read exactly from its JSON. -/
theorem requestId_eq_ok_iff {j : Json} {i : RequestId} :
    requestId j = .ok i ↔ j = requestIdJson i := by
  cases j <;> cases i <;> simp [requestId, requestIdJson, pure, Except.pure]

/-- The reader of identifiers reads back any identifier. -/
theorem requestId_requestIdJson (i : RequestId) : requestId (requestIdJson i) = .ok i :=
  requestId_eq_ok_iff.mpr rfl

/-- The reader of requests reads back any request. -/
theorem request_requestJson (r : Request) : request (requestJson r) = .ok r := by
  obtain ⟨id, method, params⟩ := r
  by_cases hp : params.isEmpty = true
  · obtain ⟨kvs, hobj, -, hmem, hd⟩ := toList_mkObj (pairs :=
      [("jsonrpc", .str "2.0"), ("id", requestIdJson id), ("method", .str method)]) (by simp)
    have h : requestJson ⟨id, method, params⟩ = .obj kvs := by
      rw [requestJson]; simp only [hp, ite_true, List.append_nil]; exact hobj
    rw [h, request]
    have hall : (kvs.toList.all fun (k, _) =>
        k == "jsonrpc" || k == "id" || k == "method" || k == "params") = true := by
      simp only [List.all_eq_true]
      rintro ⟨k, v⟩ hkv
      have := (hmem _).mp hkv
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
      rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
    have h1 := lookup_of_mem hd ((hmem ("jsonrpc", Json.str "2.0")).mpr (by simp))
    have h2 := lookup_of_mem hd ((hmem ("id", requestIdJson id)).mpr (by simp))
    have h3 := lookup_of_mem hd ((hmem ("method", Json.str method)).mpr (by simp))
    have h4 : kvs.toList.lookup "params" = none := by
      rw [List.lookup_eq_none_iff]
      rintro ⟨k, v⟩ hkv
      have := (hmem _).mp hkv
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
      rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
    have hv : jsonrpcVersion kvs.toList = true := by simp [jsonrpcVersion, h1]
    have hpe : params = [] := List.isEmpty_iff.mp hp
    subst hpe
    simp [hall, hv, h2, h3, h4, field, string, requestId_requestIdJson, bind, Except.bind, pure,
      Except.pure]
  · obtain ⟨kvs, hobj, -, hmem, hd⟩ := toList_mkObj (pairs :=
      [("jsonrpc", .str "2.0"), ("id", requestIdJson id), ("method", .str method),
        ("params", .arr params.toArray)]) (by simp)
    have h : requestJson ⟨id, method, params⟩ = .obj kvs := by
      rw [requestJson]; simp only [hp, Bool.false_eq_true, ite_false, List.cons_append,
        List.nil_append]
      exact hobj
    rw [h, request]
    have hall : (kvs.toList.all fun (k, _) =>
        k == "jsonrpc" || k == "id" || k == "method" || k == "params") = true := by
      simp only [List.all_eq_true]
      rintro ⟨k, v⟩ hkv
      have := (hmem _).mp hkv
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
      rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
    have h1 := lookup_of_mem hd ((hmem ("jsonrpc", Json.str "2.0")).mpr (by simp))
    have h2 := lookup_of_mem hd ((hmem ("id", requestIdJson id)).mpr (by simp))
    have h3 := lookup_of_mem hd ((hmem ("method", Json.str method)).mpr (by simp))
    have h4 := lookup_of_mem hd ((hmem ("params", Json.arr params.toArray)).mpr (by simp))
    have hv : jsonrpcVersion kvs.toList = true := by simp [jsonrpcVersion, h1]
    simp [hall, hv, h2, h3, h4, field, string, requestId_requestIdJson, bind, Except.bind, pure,
      Except.pure]

/-- The reader of responses reads back any response. -/
theorem response_responseJson (r : Response) : response (responseJson r) = .ok r := by
  obtain ⟨id, outcome⟩ := r
  -- The two outcomes differ only in the name and value of the third member.
  have key : ∀ (name : String) (v : Json), (name = "result" ∨ name = "error") →
      response (Json.mkObj [("jsonrpc", .str "2.0"), ("id", requestIdJson id), (name, v)]) =
        match (if name = "result" then some v else none),
            (if name = "error" then some v else none) with
        | some result, none => .ok { id, outcome := .ok result }
        | none, some e => (rpcErrorOfJson e).bind fun e => .ok { id, outcome := .error e }
        | _, _ => .error "response: not exactly one of result and error" := by
    intro name v hname
    obtain ⟨kvs, hobj, hlen, hmem, hd⟩ := toList_mkObj (pairs :=
      [("jsonrpc", .str "2.0"), ("id", requestIdJson id), (name, v)])
      (by rcases hname with rfl | rfl <;> simp)
    rw [hobj, response]
    have h1 := lookup_of_mem hd ((hmem ("jsonrpc", Json.str "2.0")).mpr (by simp))
    have h2 := lookup_of_mem hd ((hmem ("id", requestIdJson id)).mpr (by simp))
    have h3 := lookup_of_mem hd ((hmem (name, v)).mpr (by simp))
    have hv : jsonrpcVersion kvs.toList = true := by simp [jsonrpcVersion, h1]
    have hnone : ∀ other : String, other ≠ "jsonrpc" → other ≠ "id" → other ≠ name →
        kvs.toList.lookup other = none := by
      intro other o1 o2 o3
      rw [List.lookup_eq_none_iff]
      rintro ⟨k, w⟩ hkv
      have := (hmem _).mp hkv
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
      rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp_all
    rcases hname with rfl | rfl
    · have hr := h3
      have he := hnone "error" (by decide) (by decide) (by decide)
      simp [hlen, hv, hr, he, h2, field, requestId_requestIdJson, bind, Except.bind, pure,
        Except.pure]
    · have hr := hnone "result" (by decide) (by decide) (by decide)
      have he := h3
      simp [hlen, hv, hr, he, h2, field, requestId_requestIdJson, bind, Except.bind, pure,
        Except.pure]
  cases outcome with
  | ok result =>
    rw [responseJson]
    exact (key "result" result (Or.inl rfl)).trans (by simp)
  | error e =>
    rw [responseJson]
    refine (key "error" (rpcErrorJson e) (Or.inr rfl)).trans ?_
    simp [rpcErrorOfJson_json]
    rfl

/-- A JSON value reads as a request exactly when it is an object that meets the conditions below.

Its only members are `jsonrpc`, `id`, `method` and `params`, and the last may be missing.

The value of `jsonrpc` is the string `2.0`.

The values of `id` and `method` are the identifier and the method of the request.

The parameters of the request are the array under `params`, or empty when it is missing. -/
theorem request_eq_ok_iff {j : Json} {r : Request} :
    request j = .ok r ↔ ∃ kvs, j = .obj kvs ∧
      (∀ member ∈ kvs.toList, member.1 = "jsonrpc" ∨ member.1 = "id" ∨
        member.1 = "method" ∨ member.1 = "params") ∧
      kvs.toList.lookup "jsonrpc" = some (.str "2.0") ∧
      kvs.toList.lookup "id" = some (requestIdJson r.id) ∧
      kvs.toList.lookup "method" = some (.str r.method) ∧
      (kvs.toList.lookup "params" = none ∧ r.params = [] ∨
        kvs.toList.lookup "params" = some (.arr r.params.toArray)) := by
  obtain ⟨id, method, params⟩ := r
  cases j with
  | obj kvs =>
    have allIff : (kvs.toList.all fun (k, _) =>
        k == "jsonrpc" || k == "id" || k == "method" || k == "params") = true ↔
        ∀ member ∈ kvs.toList, member.1 = "jsonrpc" ∨ member.1 = "id" ∨
          member.1 = "method" ∨ member.1 = "params" := by
      simp [List.all_eq_true, or_assoc]
    have versionIff : jsonrpcVersion kvs.toList = true ↔
        kvs.toList.lookup "jsonrpc" = some (.str "2.0") := by
      unfold jsonrpcVersion
      split <;> simp_all
    simp only [request, Json.obj.injEq, exists_eq_left']
    by_cases hall : (kvs.toList.all fun (k, _) =>
        k == "jsonrpc" || k == "id" || k == "method" || k == "params") = true
    · by_cases hv : jsonrpcVersion kvs.toList = true
      · simp only [hall, hv, ↓reduceIte, versionIff.mp hv, true_and]
        rw [and_iff_right (allIff.mp hall)]
        simp only [Base.bind_ok_iff, field_eq_ok_iff, requestId_eq_ok_iff, string_eq_ok_iff]
        cases hp : kvs.toList.lookup "params" with
        | none =>
          constructor
          · rintro ⟨_, idOk, i, rfl, _, methodOk, m, rfl, h⟩
            simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq,
              Request.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨idOk, methodOk, Or.inl ⟨rfl, rfl⟩⟩
          · rintro ⟨idOk, methodOk, (⟨-, rfl⟩ | absent)⟩
            · exact ⟨_, idOk, id, rfl, _, methodOk, method, rfl, rfl⟩
            · cases absent
        | some pj =>
          cases pj with
          | arr items =>
            constructor
            · rintro ⟨_, idOk, i, rfl, _, methodOk, m, rfl, h⟩
              simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq,
                Request.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨idOk, methodOk, Or.inr (by simp)⟩
            · rintro ⟨idOk, methodOk, (⟨absent, -⟩ | given)⟩
              · cases absent
              · simp only [Option.some.injEq, Json.arr.injEq] at given
                subst given
                exact ⟨_, idOk, id, rfl, _, methodOk, method, rfl,
                  by simp [pure, Except.pure, bind, Except.bind]⟩
          | _ =>
            simp [bind, Except.bind]
      · constructor
        · intro h
          simp [hall, hv, bind, Except.bind] at h
        · rintro ⟨-, version, -⟩
          exact absurd (versionIff.mpr version) hv
    · constructor
      · intro h
        simp [hall, bind, Except.bind] at h
      · rintro ⟨members, -⟩
        exact absurd (allIff.mpr members) hall
  | _ => simp [request]

/-- A JSON value reads as a response exactly when it is an object of three members.

The value of `jsonrpc` is the string `2.0`, and the value of `id` the identifier of the response.

The third member is either `result`, whose value is the result, or `error`, an error object. -/
theorem response_eq_ok_iff {j : Json} {r : Response} :
    response j = .ok r ↔ ∃ kvs, j = .obj kvs ∧ kvs.toList.length = 3 ∧
      kvs.toList.lookup "jsonrpc" = some (.str "2.0") ∧
      kvs.toList.lookup "id" = some (requestIdJson r.id) ∧
      ((∃ result, r.outcome = .ok result ∧ kvs.toList.lookup "result" = some result ∧
          kvs.toList.lookup "error" = none) ∨
        (∃ e ej, r.outcome = .error e ∧ kvs.toList.lookup "result" = none ∧
          kvs.toList.lookup "error" = some ej ∧ rpcErrorOfJson ej = .ok e)) := by
  obtain ⟨id, outcome⟩ := r
  cases j with
  | obj kvs =>
    have versionIff : jsonrpcVersion kvs.toList = true ↔
        kvs.toList.lookup "jsonrpc" = some (.str "2.0") := by
      unfold jsonrpcVersion
      split <;> simp_all
    simp only [response, Json.obj.injEq, exists_eq_left']
    by_cases hlen : kvs.toList.length = 3
    · by_cases hv : jsonrpcVersion kvs.toList = true
      · rw [and_iff_right hlen, and_iff_right (versionIff.mp hv)]
        cases hid : kvs.toList.lookup "id" with
        | none =>
          simp [hlen, hv, hid, field, reject, throw, throwThe, MonadExceptOf.throw, bind,
            Except.bind]
        | some ij =>
          cases ij <;> cases id <;> cases outcome <;>
            cases hr : kvs.toList.lookup "result" <;> cases he : kvs.toList.lookup "error" <;>
            simp [hlen, hv, hid, field, requestId, requestIdJson, reject, throw,
              throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure]
          all_goals split <;> simp_all
      · constructor
        · intro h
          simp [hlen, hv, reject, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
        · rintro ⟨-, version, -⟩
          exact absurd (versionIff.mpr version) hv
    · constructor
      · intro h
        simp [hlen, reject, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      · rintro ⟨three, -⟩
        exact absurd three hlen
  | _ => simp [response, reject, throw, throwThe, MonadExceptOf.throw]

end EthLib.Execution.Rpc
