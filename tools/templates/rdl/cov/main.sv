{% import 'uvm_reg.sv' as uvm_reg with context %}
{%- macro top() %}
{%- for node in top_node.descendants(in_post_order=True) -%}
    {{child_cg(node)}}
{%- endfor -%}
{% endmacro -%}

{% macro child_cg(node) -%}
    {%- if isinstance(node, RegNode) -%}
        {%- if not node.is_virtual -%}
            {{uvm_reg.cg_definition(node)}}
        {%- endif -%}
    {%- endif -%}
{%- endmacro %}
