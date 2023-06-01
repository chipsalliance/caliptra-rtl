{% import 'uvm_reg.sv' as uvm_reg with context %}
{% import 'uvm_vreg.sv' as uvm_vreg with context %}
{% import 'uvm_reg_block-mem.sv' as uvm_reg_block_mem with context %}
{% import 'uvm_reg_block.sv' as uvm_reg_block with context %}


{% macro top() -%}
{{include_covergroups(top_node)}}
    {%- for node in top_node.descendants(in_post_order=True) -%}
        {{child_def(node)}}
    {%- endfor -%}
    {{child_def(top_node)}}
{{include_sample(top_node)}}
{%- endmacro %}


{% macro child_def(node) -%}
    {%- if isinstance(node, RegNode) -%}
        {%- if node.is_virtual -%}
            {{uvm_vreg.class_definition(node)}}
        {%- else -%}
            {{uvm_reg.class_definition(node)}}
        {%- endif -%}
    {%- elif isinstance(node, (RegfileNode, AddrmapNode)) -%}
        {{uvm_reg_block.class_definition(node)}}
    {%- elif isinstance(node, MemNode) -%}
        {{uvm_reg_block_mem.class_definition(node)}}
    {%- endif -%}
{%- endmacro %}

{% macro include_covergroups(node) -%}
`include "{{get_class_name(node)}}_covergroups.svh"
{%- endmacro %}

{% macro include_sample(node) -%}
`include "{{get_class_name(node)}}_sample.svh"
{%- endmacro %}
