{% import 'utils.sv' as utils with context %}

//------------------------------------------------------------------------------
// uvm_reg definition
//------------------------------------------------------------------------------
{% macro class_definition(node) -%}
{%- if class_needs_definition(node) %}
// {{get_class_friendly_name(node)}}
class {{get_class_name(node)}} extends uvm_reg;
{%- if use_uvm_factory %}
    `uvm_object_utils({{get_class_name(node)}})
{%- endif %}
    protected uvm_reg_data_t m_current;
    protected uvm_reg_data_t m_data;
    protected bit            m_is_read;
{% for field in node.fields() %}
    {{bit_covergroup_name(node)|indent}} {{bit_covergroup_inst(field)}}[{{field.width}}];
{%- endfor %}
    {{fld_covergroup_name(node)|indent}} fld_cg;
    {{child_insts(node)|indent}}
    {{function_new(node)|indent}}
    {{function_sample_values(node)|indent}}
    {{function_sample(node)|indent}}

    {{function_build(node)|indent}}
endclass : {{get_class_name(node)}}
{% endif -%}
{%- endmacro %}


//------------------------------------------------------------------------------
// Covergroup Definitions
//------------------------------------------------------------------------------
{% macro cg_definition(node) %}
{{"/*-----------------------"}} {{get_class_name(node)|upper}} {{"COVERGROUPS -----------------------*/"}}
covergroup {{bit_covergroup_name(node)}} with function sample(input bit reg_bit);
    option.per_instance = 1;
    {{bit_coverpoint()|indent}}
endgroup
covergroup {{fld_covergroup_name(node)}} with function sample({{covergroup_inputs(node)}});
    option.per_instance = 1;
    {{fld_coverpoints(node)|indent}}
endgroup
{% endmacro %}


//------------------------------------------------------------------------------
// Covergroup Inputs
//------------------------------------------------------------------------------
{% macro covergroup_inputs(node) %}
{% for field in node.fields() -%}
input bit [{{field.width}}-1:0] {{get_inst_name(field)}}{% if not loop.last %}{{","}}{% endif %}
{% endfor %}
{%- endmacro %}


//------------------------------------------------------------------------------
// Coverpoint Definitions
//------------------------------------------------------------------------------
{%- macro fld_coverpoints(node) -%}
{%- for field in node.fields() -%}
{{field_coverpoint(field)}}
{%- endfor -%}
{%- endmacro -%}


//------------------------------------------------------------------------------
// Singular Coverpoint Definition
//------------------------------------------------------------------------------
{%- macro bit_coverpoint() -%}
reg_bit_cp : coverpoint reg_bit {
    bins value[2] = {0,1};
}
reg_bit_edge_cp : coverpoint reg_bit {
    bins rise = (0 => 1);
    bins fall = (1 => 0);
}
{% endmacro %}
{%- macro field_coverpoint(field) -%}
{{get_inst_name(field)}}_cp : coverpoint {{get_inst_name(field)}};
{% endmacro %}


//------------------------------------------------------------------------------
// Child instances
//------------------------------------------------------------------------------
{% macro child_insts(node) -%}
{%- for field in node.fields() -%}
rand uvm_reg_field {{get_inst_name(field)}};
{% endfor -%}
{%- endmacro %}


//------------------------------------------------------------------------------
// new() function
//------------------------------------------------------------------------------
{% macro function_new(node) -%}
function new(string name = "{{get_class_name(node)}}");
    super.new(name, {{node.get_property('regwidth')}}, build_coverage(UVM_CVR_ALL));
endfunction : new
{%- endmacro %}


//------------------------------------------------------------------------------
// sample() function declaration
//------------------------------------------------------------------------------
{% macro function_sample(node) -%}
extern protected virtual function void sample(uvm_reg_data_t  data,
                                              uvm_reg_data_t  byte_en,
                                              bit             is_read,
                                              uvm_reg_map     map);
{%- endmacro %}


//------------------------------------------------------------------------------
// sample_values() function declaration
//------------------------------------------------------------------------------
{% macro function_sample_values(node) -%}
extern virtual function void sample_values();
{%- endmacro %}


//------------------------------------------------------------------------------
// sample() function definition
//------------------------------------------------------------------------------
{%- macro function_sample_def(node) -%}
function void {{get_class_name(node)}}::sample(uvm_reg_data_t  data,
                                               uvm_reg_data_t  byte_en,
                                               bit             is_read,
                                               uvm_reg_map     map);
    m_current = get();
    m_data    = data;
    m_is_read = is_read;
    if (get_coverage(UVM_CVR_REG_BITS)) begin
{%- for field in node.fields() %}
        foreach({{bit_covergroup_inst(field)}}[bt]) this.{{bit_covergroup_inst(field)}}[bt].sample(data[{{field.lsb}} + bt]);
{%- endfor %}
    end
    if (get_coverage(UVM_CVR_FIELD_VALS)) begin
        this.fld_cg.sample({{covergroup_sample_args(node)}});
    end
endfunction
{% endmacro -%}


//------------------------------------------------------------------------------
// sample_values() function definition
//------------------------------------------------------------------------------
{%- macro function_sample_values_def(node) -%}
function void {{get_class_name(node)}}::sample_values();
    if (get_coverage(UVM_CVR_REG_BITS)) begin
{%- for field in node.fields() %}
        foreach({{bit_covergroup_inst(field)}}[bt]) this.{{bit_covergroup_inst(field)}}[bt].sample({{get_inst_name(field)}}.get_mirrored_value() >> bt);
{%- endfor %}
    end
    if (get_coverage(UVM_CVR_FIELD_VALS)) begin
        this.fld_cg.sample({{covergroup_sample_values_args(node)}});
    end
endfunction
{% endmacro %}


//------------------------------------------------------------------------------
// build() function
//------------------------------------------------------------------------------
{% macro function_build(node) -%}
virtual function void build();
    {%- for field in node.fields() %}
    {%- if use_uvm_factory %}
    this.{{get_inst_name(field)}} = uvm_reg_field::type_id::create("{{get_inst_name(field)}}");
    {%- else %}
    this.{{get_inst_name(field)}} = new("{{get_inst_name(field)}}");
    {%- endif %}
    this.{{get_inst_name(field)}}.configure(this, {{field.width}}, {{field.lsb}}, "{{get_field_access(field)}}", {{field.is_volatile|int}}, {{"'h%x" % field.get_property('reset', default=0)}}, {{field.get_property('reset') is not none|int}}, 1, 0);
    {%- endfor %}
    if (has_coverage(UVM_CVR_REG_BITS)) begin
{%- for field in node.fields() %}
        foreach({{bit_covergroup_inst(field)}}[bt]) {{bit_covergroup_inst(field)}}[bt] = new();
{%- endfor %}
    end
    if (has_coverage(UVM_CVR_FIELD_VALS))
        fld_cg = new();
endfunction : build
{%- endmacro %}


//------------------------------------------------------------------------------
// Covergroup Name
//------------------------------------------------------------------------------
{% macro bit_covergroup_name(node)  -%} {{get_class_name(node)}}_bit_cg {%- endmacro %}
{% macro bit_covergroup_inst(field) -%} {{"%s_bit_cg"|format(get_inst_name(field))}} {%- endmacro %}
{% macro fld_covergroup_name(node)  -%} {{get_class_name(node)}}_fld_cg {%- endmacro %}


//------------------------------------------------------------------------------
// Covergroup Constructor Arguments
//------------------------------------------------------------------------------
{% macro covergroup_new_args(node) -%}
    {%- for field in node.fields() %} {{covergroup_new_arg(field)}} {% if loop.last %} {{''}} {% else %} {{","}} {% endif %} {%- endfor %}
{%- endmacro %}
{% macro covergroup_new_arg(field) -%}
    {{get_inst_name(field)}}.get_reset()
{%- endmacro %}
{% macro covergroup_sample_args(node) -%}
    {%- for field in node.fields() %} {{covergroup_sample_arg(field)}} {% if loop.last %} {{''}} {% else %} {{","}} {% endif %} {%- endfor %}
{%- endmacro %}
{% macro covergroup_sample_arg(field) -%}
    data[{{field.msb}}:{{field.lsb}}]{{"/*%s*/"|format(get_inst_name(field))}}
{%- endmacro %}
{% macro covergroup_sample_values_args(node) -%}
    {%- for field in node.fields() %} {{covergroup_sample_values_arg(field)}} {% if loop.last %} {{''}} {% else %} {{","}} {% endif %} {%- endfor %}
{%- endmacro %}
{% macro covergroup_sample_values_arg(field) -%}
    {{get_inst_name(field)}}.get_mirrored_value()
{%- endmacro %}


//------------------------------------------------------------------------------
// build() actions for uvm_reg instance (called by parent)
//------------------------------------------------------------------------------
{% macro build_instance(node) -%}
{%- if node.is_array %}
foreach(this.{{get_inst_name(node)}}[{{utils.array_iterator_list(node)}}]) begin
    {%- if use_uvm_factory %}
    this.{{get_inst_name(node)}}{{utils.array_iterator_suffix(node)}} = {{get_class_name(node)}}::type_id::create($sformatf("{{get_inst_name(node)}}{{utils.array_suffix_format(node)}}", {{utils.array_iterator_list(node)}}));
    {%- else %}
    this.{{get_inst_name(node)}}{{utils.array_iterator_suffix(node)}} = new($sformatf("{{get_inst_name(node)}}{{utils.array_suffix_format(node)}}", {{utils.array_iterator_list(node)}}));
    {%- endif %}
    this.{{get_inst_name(node)}}{{utils.array_iterator_suffix(node)}}.configure(this);
    {{add_hdl_path_slices(node, get_inst_name(node) + utils.array_iterator_suffix(node))|trim|indent}}
    this.{{get_inst_name(node)}}{{utils.array_iterator_suffix(node)}}.build();
    this.default_map.add_reg(this.{{get_inst_name(node)}}{{utils.array_iterator_suffix(node)}}, {{get_array_address_offset_expr(node)}});
end
{%- else %}
{%- if use_uvm_factory %}
this.{{get_inst_name(node)}} = {{get_class_name(node)}}::type_id::create("{{get_inst_name(node)}}");
{%- else %}
this.{{get_inst_name(node)}} = new("{{get_inst_name(node)}}");
{%- endif %}
this.{{get_inst_name(node)}}.configure(this);
{{add_hdl_path_slices(node, get_inst_name(node))|trim}}
this.{{get_inst_name(node)}}.build();
this.default_map.add_reg(this.{{get_inst_name(node)}}, {{"'h%x" % node.raw_address_offset}});
{%- endif %}
{%- endmacro %}

//------------------------------------------------------------------------------
// Load HDL path slices for this reg instance
//------------------------------------------------------------------------------
{% macro add_hdl_path_slices(node, inst_ref) -%}
{%- if node.get_property('hdl_path') %}
{{inst_ref}}.add_hdl_path_slice("{{node.get_property('hdl_path')}}", -1, -1);
{%- endif -%}

{%- if node.get_property('hdl_path_gate') %}
{{inst_ref}}.add_hdl_path_slice("{{node.get_property('hdl_path_gate')}}", -1, -1, 0, "GATE");
{%- endif -%}

{%- for field in node.fields() %}
{%- if field.get_property('hdl_path_slice') is none -%}
{%- elif field.get_property('hdl_path_slice')|length == 1 %}
{{inst_ref}}.add_hdl_path_slice("{{field.get_property('hdl_path_slice')[0]}}", {{field.lsb}}, {{field.width}});
{%- elif field.get_property('hdl_path_slice')|length == field.width %}
{%- for slice in field.get_property('hdl_path_slice') %}
{%- if field.msb > field.lsb %}
{{inst_ref}}.add_hdl_path_slice("{{slice}}", {{field.msb - loop.index0}}, 1);
{%- else %}
{{inst_ref}}.add_hdl_path_slice("{{slice}}", {{field.msb + loop.index0}}, 1);
{%- endif %}
{%- endfor %}
{%- endif %}
{%- endfor -%}

{%- for field in node.fields() %}
{%- if field.get_property('hdl_path_gate_slice') is none -%}
{%- elif field.get_property('hdl_path_gate_slice')|length == 1 %}
{{inst_ref}}.add_hdl_path_slice("{{field.get_property('hdl_path_gate_slice')[0]}}", {{field.lsb}}, {{field.width}}, 0, "GATE");
{%- elif field.get_property('hdl_path_gate_slice')|length == field.width %}
{%- for slice in field.get_property('hdl_path_gate_slice') %}
{%- if field.msb > field.lsb %}
{{inst_ref}}.add_hdl_path_slice("{{slice}}", {{field.msb - loop.index0}}, 1, 0, "GATE");
{%- else %}
{{inst_ref}}.add_hdl_path_slice("{{slice}}", {{field.msb + loop.index0}}, 1, 0, "GATE");
{%- endif %}
{%- endfor %}
{%- endif %}
{%- endfor %}
{%- endmacro %}
