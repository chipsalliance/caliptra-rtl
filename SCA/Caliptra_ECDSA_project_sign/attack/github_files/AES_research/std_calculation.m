function std_trace = std_calculation(itr,traces,mean_trace,var_trace)
    sub_trace=traces(itr,:);
    old_mean=mean_trace;
    mean_trace = mean_trace+(sub_trace-mean_trace)/itr;
    v1=sub_trace-old_mean;
    v2=sub_trace-mean_trace;
    var_trace=var_trace+v1.*v2;
    std_trace=sqrt(var_trace/i);
end