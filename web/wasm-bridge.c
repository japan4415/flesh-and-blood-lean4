#include <emscripten.h>
#include <lean/lean.h>

lean_obj_res runtime_initialize_fab_FabWasm(uint8_t builtin);
lean_obj_res fab_wtr_bounds(lean_obj_arg unit);
lean_obj_res fab_wtr_open(lean_obj_arg indices);

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
