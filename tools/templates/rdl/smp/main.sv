{%- import 'uvm_reg.sv' as uvm_reg with context -%}
{%- macro top() -%}
{%- for node in top_node.descendants(in_post_order=True) -%}
    {{child_smp(node)}}
{%- endfor -%}
{%- endmacro -%}

{%- macro child_smp(node) -%}
    {%- if isinstance(node, RegNode) -%}
        {% if not node.is_virtual %}
{{"/*-----------------------"}} {{get_class_name(node)|upper}} {{"SAMPLE FUNCTIONS -----------------------*/"}}
{{uvm_reg.function_sample_def(node)}}
{{uvm_reg.function_sample_values_def(node)}}
        {%- endif %}
    {%- endif -%}
{%- endmacro %}
