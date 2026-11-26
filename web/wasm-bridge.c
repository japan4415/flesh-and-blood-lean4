#include <emscripten.h>
#include <lean/lean.h>

lean_obj_res runtime_initialize_fab_FabWasm(uint8_t builtin);
lean_obj_res fab_wtr_bounds(lean_obj_arg unit);
lean_obj_res fab_wtr_open(lean_obj_arg indices);
lean_obj_res fab_draft_start(lean_obj_arg packs);
lean_obj_res fab_draft_pick(lean_obj_arg state, uint32_t seat, lean_obj_arg card);
lean_obj_res fab_draft_next(lean_obj_arg state);
lean_obj_res fab_draft_view(lean_obj_arg state, uint32_t seat);
lean_obj_res fab_duel_heroes(lean_obj_arg state, uint32_t seat);
lean_obj_res fab_duel_start(lean_obj_arg state, uint32_t pair, lean_obj_arg first, lean_obj_arg second, uint32_t seed);
lean_obj_res fab_duel_view(lean_obj_arg duel, uint32_t player);
lean_obj_res fab_duel_move(lean_obj_arg duel, uint32_t player, uint32_t index);

static lean_object *draft_state;
static lean_object *duels[4];

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

static void clear_state(lean_object **state) {
    if (*state) {
        lean_dec(*state);
        *state = NULL;
    }
}

EMSCRIPTEN_KEEPALIVE void fab_web_draft_reset(void) {
    clear_state(&draft_state);
    for (unsigned i = 0; i < 4; i++) clear_state(&duels[i]);
}

// A failed Lean transition leaves the current state in place.
static int accept_state(lean_object **state, lean_object *result) {
    if (lean_is_scalar(result)) {
        return 0;
    }
    lean_object *next = lean_ctor_get(result, 0);
    lean_inc(next);
    lean_dec_ref(result);
    clear_state(state);
    *state = next;
    return 1;
}

EMSCRIPTEN_KEEPALIVE int fab_web_draft_start(const char *packs) {
    return !draft_state && accept_state(&draft_state, fab_draft_start(lean_mk_string(packs)));
}

EMSCRIPTEN_KEEPALIVE int fab_web_draft_pick(uint32_t seat, const char *card) {
    if (!draft_state) return 0;
    lean_inc(draft_state);
    return accept_state(&draft_state, fab_draft_pick(draft_state, seat, lean_mk_string(card)));
}

EMSCRIPTEN_KEEPALIVE int fab_web_draft_next(void) {
    if (!draft_state) return 0;
    lean_inc(draft_state);
    return accept_state(&draft_state, fab_draft_next(draft_state));
}

EMSCRIPTEN_KEEPALIVE const char *fab_web_draft_view(uint32_t seat) {
    if (!draft_state) return "";
    lean_inc(draft_state);
    return keep_response(fab_draft_view(draft_state, seat));
}

EMSCRIPTEN_KEEPALIVE const char *fab_web_duel_heroes(uint32_t seat) {
    if (!draft_state || seat >= 8) return "";
    lean_inc(draft_state);
    return keep_response(fab_duel_heroes(draft_state, seat));
}

EMSCRIPTEN_KEEPALIVE int fab_web_duel_start(uint32_t pair, const char *first, const char *second, uint32_t seed) {
    if (!draft_state || pair >= 4 || duels[pair]) return 0;
    lean_inc(draft_state);
    return accept_state(&duels[pair], fab_duel_start(draft_state, pair, lean_mk_string(first), lean_mk_string(second), seed));
}

EMSCRIPTEN_KEEPALIVE const char *fab_web_duel_view(uint32_t seat) {
    if (seat >= 8 || !duels[seat / 2]) return "";
    lean_object *duel = duels[seat / 2];
    lean_inc(duel);
    return keep_response(fab_duel_view(duel, seat % 2));
}

EMSCRIPTEN_KEEPALIVE int fab_web_duel_move(uint32_t seat, uint32_t index) {
    if (seat >= 8 || !duels[seat / 2]) return 0;
    lean_object **duel = &duels[seat / 2];
    lean_inc(*duel);
    return accept_state(duel, fab_duel_move(*duel, seat % 2, index));
}
