#include <emscripten.h>
#include <lean/lean.h>

lean_obj_res runtime_initialize_fab_FabWasm(uint8_t builtin);
lean_obj_res fab_wtr_bounds(lean_obj_arg unit);
lean_obj_res fab_wtr_open(lean_obj_arg indices);
lean_obj_res fab_draft_start(lean_obj_arg packs);
lean_obj_res fab_draft_pick(lean_obj_arg state, uint32_t seat, lean_obj_arg card);
lean_obj_res fab_draft_next(lean_obj_arg state);
lean_obj_res fab_draft_view(lean_obj_arg state, uint32_t seat);

static lean_object *draft_state;

EMSCRIPTEN_KEEPALIVE int fab_web_init(void) {
    lean_object *result = runtime_initialize_fab_FabWasm(1);
    if (lean_io_result_is_error(result)) {
        lean_io_result_show_error(result);
        lean_dec_ref(result);
        return 0;
    }
    lean_dec_ref(result);
    lean_io_mark_end_initialization();
    return 1;
}

// ccall copies the string before another request replaces this result.
static const char *keep_response(lean_object *response) {
    static lean_object *previous;
    if (previous) {
        lean_dec(previous);
    }
    previous = response;
    return lean_string_cstr(response);
}

EMSCRIPTEN_KEEPALIVE const char *fab_web_bounds(void) {
    return keep_response(fab_wtr_bounds(lean_box(0)));
}

EMSCRIPTEN_KEEPALIVE const char *fab_web_open(const char *indices) {
    return keep_response(fab_wtr_open(lean_mk_string(indices)));
}

EMSCRIPTEN_KEEPALIVE void fab_web_draft_reset(void) {
    if (draft_state) {
        lean_dec(draft_state);
        draft_state = NULL;
    }
}

// A failed Lean transition leaves the current draft state in place.
static int accept_state(lean_object *result) {
    if (lean_is_scalar(result)) {
        return 0;
    }
    lean_object *next = lean_ctor_get(result, 0);
    lean_inc(next);
    lean_dec_ref(result);
    fab_web_draft_reset();
    draft_state = next;
    return 1;
}

EMSCRIPTEN_KEEPALIVE int fab_web_draft_start(const char *packs) {
    return !draft_state && accept_state(fab_draft_start(lean_mk_string(packs)));
}

EMSCRIPTEN_KEEPALIVE int fab_web_draft_pick(uint32_t seat, const char *card) {
    if (!draft_state) return 0;
    lean_inc(draft_state);
    return accept_state(fab_draft_pick(draft_state, seat, lean_mk_string(card)));
}

EMSCRIPTEN_KEEPALIVE int fab_web_draft_next(void) {
    if (!draft_state) return 0;
    lean_inc(draft_state);
    return accept_state(fab_draft_next(draft_state));
}

EMSCRIPTEN_KEEPALIVE const char *fab_web_draft_view(uint32_t seat) {
    if (!draft_state) return "";
    lean_inc(draft_state);
    return keep_response(fab_draft_view(draft_state, seat));
}
